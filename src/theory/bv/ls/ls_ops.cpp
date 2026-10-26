/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Operator semantics for propagation-based local search over bit-vectors.
 */

#include "theory/bv/ls/ls_ops.h"

#include <ostream>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

const char* toString(LsKind k)
{
  switch (k)
  {
    case LsKind::CONST: return "CONST";
    case LsKind::VAR: return "VAR";
    case LsKind::NOT: return "NOT";
    case LsKind::AND: return "AND";
    case LsKind::EQ: return "EQ";
    case LsKind::ULT: return "ULT";
    case LsKind::ADD: return "ADD";
    case LsKind::MUL: return "MUL";
    case LsKind::UDIV: return "UDIV";
    case LsKind::UREM: return "UREM";
    case LsKind::SHL: return "SHL";
    case LsKind::LSHR: return "LSHR";
    case LsKind::CONCAT: return "CONCAT";
    case LsKind::EXTRACT: return "EXTRACT";
    case LsKind::ITE: return "ITE";
  }
  Unreachable();
}

std::ostream& operator<<(std::ostream& os, LsKind k)
{
  return os << toString(k);
}

uint32_t arity(LsKind k)
{
  switch (k)
  {
    case LsKind::CONST:
    case LsKind::VAR: return 0;
    case LsKind::NOT:
    case LsKind::EXTRACT: return 1;
    case LsKind::AND:
    case LsKind::EQ:
    case LsKind::ULT:
    case LsKind::ADD:
    case LsKind::MUL:
    case LsKind::UDIV:
    case LsKind::UREM:
    case LsKind::SHL:
    case LsKind::LSHR:
    case LsKind::CONCAT: return 2;
    case LsKind::ITE: return 3;
  }
  Unreachable();
}

namespace {

/** Return the width-1 value of b. */
LsValue mkBool(bool b) { return LsValue(1, static_cast<uint32_t>(b)); }

/*
 * Probabilities (per mille) of the biased choices inside the rules. All are
 * Bitwuzla's values; none comes from the papers. They are candidates for
 * recalibration and will become expert options.
 */
/** EXTRACT inverse: keep the current bits outside [hi:lo]. */
constexpr uint32_t kProbExtractKeep = 500;
/** UDIV pos 0 inverse: return the smallest solution s * t. */
constexpr uint32_t kProbUdivLo = 500;
/** UREM pos 0 consistent: return t instead of a value in [2t+1, ones]. */
constexpr uint32_t kProbUremConsT = 100;
/** UREM pos 1 inverse with s = t: return 0 instead of a value > t. */
constexpr uint32_t kProbUremInvZero = 250;
/** UREM pos 1 inverse with s > t: return n = s - t itself. */
constexpr uint32_t kProbUremInvN = 500;
/** UREM pos 1 inverse with s > t = 0: return 1. */
constexpr uint32_t kProbUremInvOne = 100;
/** UREM pos 1 consistent: return 0 instead of a value > t. */
constexpr uint32_t kProbUremConsZero = 100;
/** Maximum number of trial divisions when searching a divisor for UREM. */
constexpr uint32_t kMaxDivisorTrials = 256;

}  // namespace

LsValue evaluate(const OpInfo& op, const std::vector<const LsValue*>& ch)
{
  Assert(ch.size() == arity(op.kind));
  Assert(op.kind == LsKind::CONCAT || op.kind == LsKind::EXTRACT
         || op.kind == LsKind::ITE || ch.size() < 2
         || ch[0]->getSize() == ch[1]->getSize());
  switch (op.kind)
  {
    case LsKind::NOT: return ~*ch[0];
    case LsKind::AND: return *ch[0] & *ch[1];
    case LsKind::EQ: return mkBool(*ch[0] == *ch[1]);
    case LsKind::ULT: return mkBool(ch[0]->unsignedLessThan(*ch[1]));
    case LsKind::ADD: return *ch[0] + *ch[1];
    case LsKind::MUL: return *ch[0] * *ch[1];
    case LsKind::UDIV: return ch[0]->unsignedDivTotal(*ch[1]);
    case LsKind::UREM: return ch[0]->unsignedRemTotal(*ch[1]);
    case LsKind::SHL: return ch[0]->leftShift(*ch[1]);
    case LsKind::LSHR: return ch[0]->logicalRightShift(*ch[1]);
    case LsKind::CONCAT: return ch[0]->concat(*ch[1]);
    case LsKind::EXTRACT:
      Assert(op.lo <= op.hi && op.hi < ch[0]->getSize());
      return ch[0]->extract(op.hi, op.lo);
    case LsKind::ITE:
      Assert(ch[0]->getSize() == 1);
      Assert(ch[1]->getSize() == ch[2]->getSize());
      return ch[0]->isBitSet(0) ? *ch[1] : *ch[2];
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "evaluate called on leaf kind " << op.kind;
}

namespace {

/** For CONCAT: the part of t that child posX must equal. */
LsValue concatPartOf(uint32_t posX,
                     const LsValue& t,
                     const std::vector<const LsValue*>& ch)
{
  uint32_t w = t.getSize();
  if (posX == 0)
  {
    return t.extract(w - 1, ch[1]->getSize());
  }
  return t.extract(ch[1]->getSize() - 1, 0);
}

/** For ITE: return true if posX is the branch selected by the condition. */
bool iteIsEnabled(uint32_t posX, const std::vector<const LsValue*>& ch)
{
  Assert(posX == 1 || posX == 2);
  return ch[0]->isBitSet(0) == (posX == 1);
}

/*
 * SHL and LSHR are mirror images: SHL counts trailing zeros, shifts left and
 * loses the top bits of x, LSHR counts leading zeros, shifts right and loses
 * the bottom bits. The helpers below take left = true for SHL.
 */

/** Return x shifted by k <= w bits, to the left if left holds. */
LsValue shiftBy(const LsValue& x, uint32_t k, bool left)
{
  LsValue amount(x.getSize(), k);
  return left ? x.leftShift(amount) : x.logicalRightShift(amount);
}

/** Return the number of zeros that a shift in direction left fills in. */
uint32_t shiftZeros(const LsValue& x, bool left)
{
  return left ? ctz(x) : clz(x);
}

/**
 * Return x with its k bits that a shift in direction left loses (the top k
 * if left, the bottom k otherwise) randomized.
 */
LsValue randomizeLostBits(const LsValue& x, uint32_t k, bool left, LsRng& rng)
{
  if (k == 0)
  {
    return x;
  }
  uint32_t w = x.getSize();
  uint32_t lo = left ? w - k : 0;
  return setSlice(x, lo + k - 1, lo, rng.randomValue(k));
}

/** IC for x << s = t (left) or x >> s = t (not left), x at position 0. */
bool icShiftValue(const LsValue& s, const LsValue& t, bool left)
{
  uint32_t k = shiftAmount(s, t.getSize());
  return shiftBy(shiftBy(t, k, !left), k, left) == t;
}

/** IC for s << x = t (left) or s >> x = t (not left), x at position 1. */
bool icShiftAmount(const LsValue& s, const LsValue& t, bool left)
{
  uint32_t zs = shiftZeros(s, left);
  uint32_t zt = shiftZeros(t, left);
  return zs <= zt && (isZero(t) || shiftBy(s, zt - zs, left) == t);
}

/** Inverse value for a shift, see icShiftValue and icShiftAmount. */
LsValue invShift(uint32_t posX,
                 const LsValue& t,
                 const std::vector<const LsValue*>& ch,
                 bool left,
                 LsRng& rng)
{
  uint32_t w = t.getSize();
  if (posX == 0)
  {
    // Undo the shift; the bits shifted out are free.
    uint32_t k = shiftAmount(*ch[1], w);
    return randomizeLostBits(shiftBy(t, k, !left), k, left, rng);
  }
  const LsValue& s = *ch[0];
  if (isZero(t))
  {
    if (isZero(s))
    {
      return rng.randomValue(w);
    }
    // Every amount that shifts all set bits of s out.
    return rng.randomInRange(LsValue(w, w - shiftZeros(s, left)),
                             LsValue::mkOnes(w));
  }
  // The amount is unique.
  return LsValue(w, shiftZeros(t, left) - shiftZeros(s, left));
}

/** Consistent value for a shift. */
LsValue consShift(uint32_t posX, const LsValue& t, bool left, LsRng& rng)
{
  uint32_t w = t.getSize();
  if (isZero(t))
  {
    return rng.randomValue(w);
  }
  uint32_t zt = shiftZeros(t, left);
  if (posX == 0)
  {
    // Any amount k <= zt works with x = t shifted back by k.
    uint32_t k = rng.pickIndex(zt + 1);
    return randomizeLostBits(shiftBy(t, k, !left), k, left, rng);
  }
  return rng.randomInRange(LsValue::mkZero(w), LsValue(w, zt));
}

/** Inverse value for x * s = t (MUL is commutative). */
LsValue invMul(const LsValue& s, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  if (isZero(s))
  {
    return rng.randomValue(w);
  }
  // With s = s' * 2^c and s' odd, x * s' = t / 2^c modulo 2^(w-c): the low
  // w-c bits of x are determined, the top c bits are free.
  uint32_t c = ctz(s);
  LsValue y = shiftBy(t, c, false) * modInverse(shiftBy(s, c, false));
  return randomizeLostBits(y, c, true, rng);
}

/** Consistent value for MUL: any x with ctz(x) <= ctz(t). */
LsValue consMul(const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue x = rng.randomValue(w);
  uint32_t zt = ctz(t);
  if (!isZero(t) && ctz(x) > zt)
  {
    uint32_t i = rng.pickIndex(zt + 1);
    x = setSlice(x, i, i, LsValue::mkOne(1));
  }
  return x;
}

/** IC for x / s = t (posX = 0) or s / x = t (posX = 1). */
bool icUdiv(uint32_t posX, const LsValue& s, const LsValue& t)
{
  if (posX == 0)
  {
    return (s * t).unsignedDivTotal(s) == t;
  }
  return s.unsignedDivTotal(s.unsignedDivTotal(t)) == t;
}

/** Inverse value for UDIV, see icUdiv. */
LsValue invUdiv(uint32_t posX, const LsValue& s, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue ones = LsValue::mkOnes(w);
  if (posX == 0)
  {
    if (isZero(s))
    {
      return rng.randomValue(w);  // t = ones
    }
    // x in [s*t, s*(t+1) - 1], capped at ones.
    LsValue lo = s * t;
    if (rng.pickWithProb(kProbUdivLo))
    {
      return lo;
    }
    bool capped = isOnes(t) || umulOverflow(s, inc(t));
    LsValue hi = capped ? ones : dec(s * inc(t));
    return rng.randomInRange(lo, hi);
  }
  if (isOnes(t))
  {
    // s / 0 = ones, and s / 1 = ones iff s = ones.
    LsValue zero = LsValue::mkZero(w);
    return isOnes(s) ? rng.randomInRange(zero, LsValue::mkOne(w)) : zero;
  }
  if (isZero(t))
  {
    return rng.randomInRange(inc(s), ones);
  }
  return rng.randomInRange(inc(s.unsignedDivTotal(inc(t))),
                           s.unsignedDivTotal(t));
}

/** Consistent value for UDIV. */
LsValue consUdiv(uint32_t posX, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue one = LsValue::mkOne(w);
  LsValue ones = LsValue::mkOnes(w);
  if (posX == 0)
  {
    if (isOnes(t))
    {
      return rng.randomValue(w);  // x / 0 = ones
    }
    if (isZero(t))
    {
      return rng.randomInRange(zero, dec(ones));
    }
    if (t == one)
    {
      return rng.randomInRange(one, ones);
    }
    // x = y*t + o with divisor y and remainder o < y, without overflow.
    LsValue y = rng.randomInRange(one, ones.unsignedDivTotal(t));
    LsValue yt = y * t;
    LsValue maxOffset = dec(y);
    LsValue room = ones - yt;
    if (room.unsignedLessThan(maxOffset))
    {
      maxOffset = room;
    }
    return yt + rng.randomInRange(zero, maxOffset);
  }
  if (isOnes(t))
  {
    return rng.randomInRange(zero, one);  // s' / 0 or ones / 1
  }
  if (isZero(t))
  {
    return rng.randomInRange(one, ones);  // 0 / x
  }
  return rng.randomInRange(one, ones.unsignedDivTotal(t));  // (x*t) / x
}

/** IC for x mod s = t (posX = 0) or s mod x = t (posX = 1). */
bool icUrem(uint32_t posX, const LsValue& s, const LsValue& t)
{
  if (posX == 0)
  {
    // ~(-s) >= t, i.e., s = 0 or t < s.
    return !(~(-s)).unsignedLessThan(t);
  }
  return !((t + t - s) & s).unsignedLessThan(t);
}

/**
 * Return a random divisor d > t of n, or n if the bounded trial division
 * finds none. Requires n > t.
 */
LsValue randomDivisorAbove(const LsValue& n, const LsValue& t, LsRng& rng)
{
  uint32_t w = n.getSize();
  const Integer& nv = n.getValue();
  const Integer& tv = t.getValue();
  std::vector<Integer> divisors;
  for (uint32_t i = 1; i <= kMaxDivisorTrials; ++i)
  {
    Integer d(i);
    if (d * d > nv)
    {
      break;
    }
    if (nv.euclidianDivideRemainder(d).isZero())
    {
      Integer q = nv.euclidianDivideQuotient(d);
      if (d > tv)
      {
        divisors.push_back(d);
      }
      if (q > tv && q != d)
      {
        divisors.push_back(q);
      }
    }
  }
  if (divisors.empty())
  {
    return n;
  }
  return LsValue(w, divisors[rng.pickIndex(divisors.size())]);
}

/** Inverse value for UREM, see icUrem. */
LsValue invUrem(uint32_t posX, const LsValue& s, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue ones = LsValue::mkOnes(w);
  if (posX == 0)
  {
    if (isZero(s))
    {
      return t;  // x mod 0 = x
    }
    // x = s*n + t for any n that does not overflow.
    LsValue n = rng.randomInRange(zero, (ones - t).unsignedDivTotal(s));
    return s * n + t;
  }
  if (isOnes(t))
  {
    return zero;  // s mod 0 = s = ones
  }
  if (s == t)
  {
    // s mod 0 = s, and s mod x = s for every x > s.
    return rng.pickWithProb(kProbUremInvZero) ? zero
                                              : rng.randomInRange(inc(t), ones);
  }
  // s > t: x > t must divide n = s - t.
  LsValue n = s - t;
  if (rng.pickWithProb(kProbUremInvN))
  {
    return n;
  }
  if (isZero(t) && rng.pickWithProb(kProbUremInvOne))
  {
    return LsValue::mkOne(w);
  }
  return randomDivisorAbove(n, t, rng);
}

/** Consistent value for UREM. */
LsValue consUrem(uint32_t posX, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue ones = LsValue::mkOnes(w);
  if (posX == 0)
  {
    // The consistent values are t (with s = 0 or s > t) and [2t+1, ones]
    // (with s = x - t).
    if (isOnes(t) || uaddOverflow(t, inc(t))
        || rng.pickWithProb(kProbUremConsT))
    {
      return t;
    }
    return rng.randomInRange(t + inc(t), ones);
  }
  // The consistent values are 0 (with s = t) and [t+1, ones] (with s = t).
  if (isOnes(t) || rng.pickWithProb(kProbUremConsZero))
  {
    return zero;
  }
  return rng.randomInRange(inc(t), ones);
}

/** Inverse value for (x <u s) = t (posX = 0) or (s <u x) = t (posX = 1). */
LsValue invUlt(uint32_t posX,
               const LsValue& t,
               const std::vector<const LsValue*>& ch,
               LsRng& rng)
{
  const LsValue& s = *ch[1 - posX];
  uint32_t w = s.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue ones = LsValue::mkOnes(w);
  bool lt = t.isBitSet(0);
  if (posX == 0)
  {
    return lt ? rng.randomInRange(zero, dec(s)) : rng.randomInRange(s, ones);
  }
  return lt ? rng.randomInRange(inc(s), ones) : rng.randomInRange(zero, s);
}

/** Consistent value for ULT, see invUlt. */
LsValue consUlt(uint32_t posX, const LsValue& t, uint32_t w, LsRng& rng)
{
  if (!t.isBitSet(0))
  {
    return rng.randomValue(w);
  }
  // x <u s' needs x != ones, s' <u x needs x != 0.
  LsValue zero = LsValue::mkZero(w);
  LsValue ones = LsValue::mkOnes(w);
  return posX == 0 ? rng.randomInRange(zero, dec(ones))
                   : rng.randomInRange(inc(zero), ones);
}

/** The inverse value rules, see inverseValue. */
LsValue computeInverse(const OpInfo& op,
                       uint32_t posX,
                       const LsValue& t,
                       const std::vector<const LsValue*>& ch,
                       LsRng& rng)
{
  uint32_t w = ch[posX]->getSize();
  switch (op.kind)
  {
    case LsKind::NOT: return ~t;
    case LsKind::AND:
      // Bits where s is 1 must equal t, the others are free.
      return t | (rng.randomValue(w) & ~*ch[1 - posX]);
    case LsKind::EQ:
      return t.isBitSet(0) ? *ch[1 - posX] : rng.randomNotEqual(*ch[1 - posX]);
    case LsKind::ADD: return t - *ch[1 - posX];
    case LsKind::CONCAT: return concatPartOf(posX, t, ch);
    case LsKind::EXTRACT:
    {
      // Keep the bits outside [hi:lo] with probability 1/2.
      LsValue x =
          rng.pickWithProb(kProbExtractKeep) ? *ch[0] : rng.randomValue(w);
      return setSlice(x, op.hi, op.lo, t);
    }
    case LsKind::ITE:
    {
      if (posX > 0)
      {
        return t;
      }
      bool a = *ch[1] == t;
      bool b = *ch[2] == t;
      return a && b ? rng.randomValue(1) : mkBool(a);
    }
    case LsKind::ULT: return invUlt(posX, t, ch, rng);
    case LsKind::SHL: return invShift(posX, t, ch, true, rng);
    case LsKind::LSHR: return invShift(posX, t, ch, false, rng);
    case LsKind::MUL: return invMul(*ch[1 - posX], t, rng);
    case LsKind::UDIV: return invUdiv(posX, *ch[1 - posX], t, rng);
    case LsKind::UREM: return invUrem(posX, *ch[1 - posX], t, rng);
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "inverseValue called on leaf kind " << op.kind;
}

}  // namespace

bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const std::vector<const LsValue*>& ch)
{
  Assert(ch.size() == arity(op.kind));
  Assert(posX < ch.size());
  switch (op.kind)
  {
    case LsKind::NOT:
    case LsKind::EQ:
    case LsKind::ADD:
    case LsKind::EXTRACT: return true;
    case LsKind::AND: return (t & *ch[1 - posX]) == t;
    case LsKind::CONCAT:
    {
      // The other child must equal the rest of t.
      uint32_t w = t.getSize();
      if (posX == 0)
      {
        return *ch[1] == t.extract(ch[1]->getSize() - 1, 0);
      }
      return *ch[0] == t.extract(w - 1, ch[1]->getSize());
    }
    case LsKind::ITE:
      if (posX == 0)
      {
        return *ch[1] == t || *ch[2] == t;
      }
      // The disabled branch is never a propagation path, so it counts as not
      // invertible.
      return iteIsEnabled(posX, ch);
    case LsKind::ULT:
      // x <u s needs s != 0 and s <u x needs s != ones to be true.
      if (!t.isBitSet(0))
      {
        return true;
      }
      return posX == 0 ? !isZero(*ch[1]) : !isOnes(*ch[0]);
    case LsKind::SHL:
    case LsKind::LSHR:
    {
      bool left = op.kind == LsKind::SHL;
      return posX == 0 ? icShiftValue(*ch[1], t, left)
                       : icShiftAmount(*ch[0], t, left);
    }
    case LsKind::MUL:
      // t = 0, or s != 0 and ctz(s) <= ctz(t) (ctz(0) = w covers both).
      return ctz(*ch[1 - posX]) <= ctz(t);
    case LsKind::UDIV: return icUdiv(posX, *ch[1 - posX], t);
    case LsKind::UREM: return icUrem(posX, *ch[1 - posX], t);
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "isInvertible called on leaf kind " << op.kind;
}

bool isEssential(const OpInfo& op,
                 uint32_t i,
                 const LsValue& t,
                 const std::vector<const LsValue*>& ch)
{
  Assert(ch.size() == arity(op.kind));
  Assert(i < ch.size());
  for (uint32_t j = 0, n = ch.size(); j < n; ++j)
  {
    if (j != i && isInvertible(op, j, t, ch))
    {
      return false;
    }
  }
  return true;
}

LsValue inverseValue(const OpInfo& op,
                     uint32_t posX,
                     const LsValue& t,
                     const std::vector<const LsValue*>& ch,
                     LsRng& rng)
{
  Assert(isInvertible(op, posX, t, ch));
  LsValue x = computeInverse(op, posX, t, ch, rng);
#ifdef CVC5_ASSERTIONS
  std::vector<const LsValue*> chx = ch;
  chx[posX] = &x;
  Assert(evaluate(op, chx) == t) << "inverse value " << x << " for " << op.kind
                                 << " at " << posX << " does not produce " << t;
#endif
  return x;
}

LsValue consistentValue(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const std::vector<const LsValue*>& ch,
                        LsRng& rng)
{
  Assert(ch.size() == arity(op.kind));
  Assert(posX < ch.size());
  uint32_t w = ch[posX]->getSize();
  switch (op.kind)
  {
    case LsKind::NOT: return ~t;
    case LsKind::AND: return t | rng.randomValue(w);
    case LsKind::EQ:
    case LsKind::ADD: return rng.randomValue(w);
    case LsKind::CONCAT: return concatPartOf(posX, t, ch);
    case LsKind::EXTRACT: return setSlice(rng.randomValue(w), op.hi, op.lo, t);
    case LsKind::ITE:
      // For a branch, t is consistent (with the condition selecting it).
      return posX == 0 ? rng.randomValue(1) : t;
    case LsKind::ULT: return consUlt(posX, t, w, rng);
    case LsKind::SHL: return consShift(posX, t, true, rng);
    case LsKind::LSHR: return consShift(posX, t, false, rng);
    case LsKind::MUL: return consMul(t, rng);
    case LsKind::UDIV: return consUdiv(posX, t, rng);
    case LsKind::UREM: return consUrem(posX, t, rng);
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "consistentValue called on leaf kind " << op.kind;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
