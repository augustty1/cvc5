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

#include <algorithm>
#include <optional>
#include <ostream>
#include <utility>

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
    case LsKind::XOR: return "XOR";
    case LsKind::SEXT: return "SEXT";
    case LsKind::ASHR: return "ASHR";
    case LsKind::SLT: return "SLT";
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
    case LsKind::EXTRACT:
    case LsKind::SEXT: return 1;
    case LsKind::AND:
    case LsKind::EQ:
    case LsKind::ULT:
    case LsKind::ADD:
    case LsKind::MUL:
    case LsKind::UDIV:
    case LsKind::UREM:
    case LsKind::SHL:
    case LsKind::LSHR:
    case LsKind::CONCAT:
    case LsKind::XOR:
    case LsKind::ASHR:
    case LsKind::SLT: return 2;
    case LsKind::ITE: return 3;
  }
  Unreachable();
}

namespace {

/** Return the width-1 value of b. */
LsValue mkBool(bool b) { return LsValue(1, b ? 1 : 0); }

/*
 * SLT (prop-cb+): x <s y iff f(x) <u f(y), with f the flip of the most
 * significant bit. f is a bijection on the values of a width, and a value v
 * matches a domain x iff f(v) matches flipMsbD(x), so the rules of SLT are
 * the rules of ULT on the flipped values and domains, with the values they
 * return flipped back (plan D39).
 */

/** Return v with its most significant bit flipped. */
LsValue flipMsb(const LsValue& v)
{
  return v ^ LsValue::mkMinSigned(v.getSize());
}

/** Return the domain of the values f(v) for v matching x. */
TernaryDomain flipMsbD(const TernaryDomain& x)
{
  uint32_t w = x.getSize();
  if (!x.isFixedBit(w - 1))
  {
    return x;
  }
  LsValue m = LsValue::mkMinSigned(w);
  return TernaryDomain(x.lo() ^ m, x.hi() ^ m);
}

/** The children of an SLT with their most significant bits flipped. */
class FlippedChildren
{
 public:
  explicit FlippedChildren(const LsChildren& ch)
      : d_a(flipMsb(*ch[0])), d_b(flipMsb(*ch[1]))
  {
    d_ch.push_back(&d_a);
    d_ch.push_back(&d_b);
  }
  FlippedChildren(const FlippedChildren&) = delete;
  FlippedChildren& operator=(const FlippedChildren&) = delete;
  const LsChildren& get() const { return d_ch; }

 private:
  LsValue d_a;
  LsValue d_b;
  LsChildren d_ch;
};

/** The operator whose rules SLT uses. */
const OpInfo kUltOp{LsKind::ULT};

/**
 * Return x shifted right arithmetically by k bits: the bits shifted in are
 * copies of the most significant bit, all of them if k >= w.
 */
LsValue ashrBy(const LsValue& x, uint32_t k)
{
  return msb(x) ? ~(~x).logicalRightShift(k) : x.logicalRightShift(k);
}

/** Return x sign-extended by n >= 1 bits. */
LsValue signExtend(const LsValue& x, uint32_t n)
{
  return (msb(x) ? LsValue::mkOnes(n) : LsValue::mkZero(n)).concat(x);
}

/*
 * Probabilities (per mille) of the biased choices inside the rules. Neither
 * paper specifies them; all are taken from Bitwuzla (src/ls/bv), and all are
 * candidates for recalibration and will become expert options.
 */
/** EXTRACT inverse: keep the current bits outside [hi:lo]. */
constexpr uint32_t kProbExtractKeep = 500;
/**
 * EXTRACT inverse, when not keeping: set the bits outside [hi:lo] randomly;
 * otherwise each of the two outer slices is set to all zeros or all ones.
 */
constexpr uint32_t kProbExtractRandom = 500;
/** MUL consistent with t even and nonzero: return 2^n with n < ctz(t). */
constexpr uint32_t kProbMulConsPow2 = 100;
/** MUL consistent with t even and nonzero: return t >> r with r <= ctz(t). */
constexpr uint32_t kProbMulConsShift = 100;
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

/*
 * Bounds of the rules modulo constant bits.
 */
/**
 * UDIV pos 0 consistent: return t when it matches the domain. The other
 * stages never draw t, so this keeps its probability above zero (plan D9).
 */
constexpr uint32_t kProbUdivConsT = 100;
/** UDIV pos 0 consistent: random divisors tried first (as in Bitwuzla). */
constexpr uint32_t kUdivConsTries = 20;
/**
 * Steps of the bounded deterministic searches. A search that runs out of
 * steps may miss a value, but never returns a wrong one.
 */
constexpr uint32_t kSearchLimit = 100;
/**
 * UREM pos 1 inverse: draw values of (t, s - t] that divide s - t instead of
 * taking a divisor that the bounded search finds. This keeps the divisors
 * that the search misses reachable (plan D19).
 */
constexpr uint32_t kProbUremInvSample = 100;
/** UREM pos 1 inverse: the number of values drawn there. */
constexpr uint32_t kUremDivisorSamples = 16;
/**
 * UREM pos 0 inverse: the number of uniform multipliers tried before the
 * deterministic search, so that every solution keeps a non-zero probability.
 */
constexpr uint32_t kUremMultiplierTries = 32;

}  // namespace

LsValue evaluate(const OpInfo& op, const LsChildren& ch)
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
    case LsKind::SLT:
      return mkBool(flipMsb(*ch[0]).unsignedLessThan(flipMsb(*ch[1])));
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
    case LsKind::XOR: return *ch[0] ^ *ch[1];
    case LsKind::SEXT: Assert(op.hi >= 1); return signExtend(*ch[0], op.hi);
    case LsKind::ASHR:
      return ashrBy(*ch[0], shiftAmount(*ch[1], ch[0]->getSize()));
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "evaluate called on leaf kind " << op.kind;
}

namespace {

/** For CONCAT: the part of t that child posX must equal. */
LsValue concatPartOf(uint32_t posX, const LsValue& t, const LsChildren& ch)
{
  uint32_t w = t.getSize();
  if (posX == 0)
  {
    return t.extract(w - 1, ch[1]->getSize());
  }
  return t.extract(ch[1]->getSize() - 1, 0);
}

/**
 * For SEXT: return true if t is the sign extension of a value of width w, i.e.,
 * its bits from w - 1 up are all 0 or all 1 (FMCAD'20 Table III).
 */
bool isSignExtension(const LsValue& t, uint32_t w)
{
  LsValue top = t.extract(t.getSize() - 1, w - 1);
  return isZero(top) || isOnes(top);
}

/** For ITE: return true if posX is the branch selected by the condition. */
bool iteIsEnabled(uint32_t posX, const LsChildren& ch)
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
  return left ? x.leftShift(k) : x.logicalRightShift(k);
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
                 const LsChildren& ch,
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

/*
 * ASHR (FMCAD'20 Tables III and V). At position 0, x >>a s = t needs the top
 * k + 1 bits of t to be equal for the amount k = s < w (they are copies of
 * the sign of x), and t in {0, ones} for k >= w. At position 1, s >>a x = t is
 * s >> x = t if s[msb] = 0 and ~s >> x = ~t otherwise, so its rules are those
 * of LSHR on the values that ashrAsLshr returns.
 */

/** The number of top bits of t equal to its most significant bit. */
uint32_t signRun(const LsValue& t) { return msb(t) ? clz(~t) : clz(t); }

/** The base IC for x >>a s = t, x at position 0. */
bool icAshrValue(const LsValue& s, const LsValue& t)
{
  uint32_t w = t.getSize();
  uint32_t k = shiftAmount(s, w);
  return k >= w ? isZero(t) || isOnes(t) : signRun(t) > k;
}

/**
 * A value v with v >>a k = t, which icAshrValue requires to exist: t shifted
 * back with the k bits shifted out drawn, or for k >= w (t is 0 or ones) a
 * value with the sign of t and the other bits drawn.
 */
LsValue invAshrValue(uint32_t k, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  if (k >= w)
  {
    return setSlice(rng.randomValue(w), w - 1, w - 1, mkBool(msb(t)));
  }
  return randomizeLostBits(t.leftShift(k), k, false, rng);
}

/** s and t, complemented if s[msb] = 1: s >>a x = t iff s' >> x = t'. */
std::pair<LsValue, LsValue> ashrAsLshr(const LsValue& s, const LsValue& t)
{
  return msb(s) ? std::make_pair(~s, ~t) : std::make_pair(s, t);
}

/**
 * Consistent value for ASHR. Position 0: for t in {0, ones}, any value with
 * the sign of t (with an amount >= w); otherwise an amount k < signRun(t),
 * drawn uniformly, and a value as the inverse value for it. Position 1: any
 * amount for t in {0, ones} (s' = t), otherwise one below signRun(t).
 */
LsValue consAshr(uint32_t posX, const LsValue& t, LsRng& rng)
{
  uint32_t w = t.getSize();
  bool constant = isZero(t) || isOnes(t);
  if (posX == 0)
  {
    return invAshrValue(constant ? w : rng.pickIndex(signRun(t)), t, rng);
  }
  if (constant)
  {
    return rng.randomValue(w);
  }
  return rng.randomInRange(LsValue::mkZero(w), LsValue(w, signRun(t) - 1));
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
  if (isZero(t))
  {
    return rng.randomValue(w);
  }
  LsValue one = LsValue::mkOne(1);
  LsValue x = rng.randomInRange(LsValue::mkOne(w), LsValue::mkOnes(w));
  if (t.isBitSet(0))
  {
    return setSlice(x, 0, 0, one);  // t odd: x odd
  }
  uint32_t zt = ctz(t);
  if (rng.pickWithProb(kProbMulConsPow2))
  {
    uint32_t n = rng.pickIndex(zt);
    return setSlice(LsValue::mkZero(w), n, n, one);
  }
  if (rng.pickWithProb(kProbMulConsShift))
  {
    return t.logicalRightShift(rng.pickIndex(zt + 1));
  }
  if (ctz(x) > zt)
  {
    uint32_t i = rng.pickIndex(zt);
    x = setSlice(x, i, i, one);
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
  return randomDivisorAbove(n, t, rng, kMaxDivisorTrials);
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
               const LsChildren& ch,
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
                       const LsChildren& ch,
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
      // The bits outside [hi:lo]: keep them, randomize them, or set each
      // outer slice to all zeros or all ones.
      LsValue x = *ch[0];
      if (!rng.pickWithProb(kProbExtractKeep))
      {
        if (rng.pickWithProb(kProbExtractRandom))
        {
          x = rng.randomValue(w);
        }
        else
        {
          if (op.hi + 1 < w)
          {
            uint32_t size = w - 1 - op.hi;
            x = setSlice(
                x,
                w - 1,
                op.hi + 1,
                rng.flipCoin() ? LsValue::mkZero(size) : LsValue::mkOnes(size));
          }
          if (op.lo > 0)
          {
            x = setSlice(x,
                         op.lo - 1,
                         0,
                         rng.flipCoin() ? LsValue::mkZero(op.lo)
                                        : LsValue::mkOnes(op.lo));
          }
        }
      }
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
    // x ^ s = t: the only solution is s ^ t (XOR is commutative).
    case LsKind::XOR: return t ^ *ch[1 - posX];
    // sext(x) = t: the only solution is the low w bits of t.
    case LsKind::SEXT: return t.extract(w - 1, 0);
    case LsKind::ASHR:
    {
      if (posX == 0)
      {
        return invAshrValue(shiftAmount(*ch[1], w), t, rng);
      }
      auto [s, tl] = ashrAsLshr(*ch[0], t);
      LsChildren chl{&s, ch[1]};
      return invShift(1, tl, chl, false, rng);
    }
    case LsKind::CONST:
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "inverseValue called on leaf kind " << op.kind;
}

}  // namespace

bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const LsChildren& ch)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    return isInvertible(kUltOp, posX, t, f.get());
  }
  Assert(ch.size() == arity(op.kind));
  Assert(posX < ch.size());
  switch (op.kind)
  {
    case LsKind::NOT:
    case LsKind::EQ:
    case LsKind::ADD:
    case LsKind::EXTRACT:
    case LsKind::XOR: return true;
    case LsKind::AND: return (t & *ch[1 - posX]) == t;
    case LsKind::SEXT: return isSignExtension(t, ch[0]->getSize());
    case LsKind::ASHR:
    {
      if (posX == 0)
      {
        return icAshrValue(*ch[1], t);
      }
      auto [s, tl] = ashrAsLshr(*ch[0], t);
      return icShiftAmount(s, tl, false);
    }
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
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "isInvertible called on leaf kind " << op.kind;
}

bool isEssential(const OpInfo& op,
                 uint32_t i,
                 const LsValue& t,
                 const LsChildren& ch)
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
                     const LsChildren& ch,
                     LsRng& rng)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    return flipMsb(inverseValue(kUltOp, posX, t, f.get(), rng));
  }
  Assert(isInvertible(op, posX, t, ch));
  LsValue x = computeInverse(op, posX, t, ch, rng);
#ifdef CVC5_ASSERTIONS
  LsChildren chx = ch;
  chx[posX] = &x;
  Assert(evaluate(op, chx) == t) << "inverse value " << x << " for " << op.kind
                                 << " at " << posX << " does not produce " << t;
#endif
  return x;
}

LsValue consistentValue(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const LsChildren& ch,
                        LsRng& rng)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    return flipMsb(consistentValue(kUltOp, posX, t, f.get(), rng));
  }
  Assert(ch.size() == arity(op.kind));
  Assert(posX < ch.size());
  uint32_t w = ch[posX]->getSize();
  switch (op.kind)
  {
    case LsKind::NOT: return ~t;
    case LsKind::AND: return t | rng.randomValue(w);
    case LsKind::EQ:
    case LsKind::ADD:
    case LsKind::XOR: return rng.randomValue(w);
    case LsKind::CONCAT: return concatPartOf(posX, t, ch);
    case LsKind::EXTRACT: return setSlice(rng.randomValue(w), op.hi, op.lo, t);
    case LsKind::SEXT:
      // Unary: the only consistent value is the inverse value.
      Assert(isInvertible(op, posX, t, ch));
      return t.extract(w - 1, 0);
    case LsKind::ASHR: return consAshr(posX, t, rng);
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
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "consistentValue called on leaf kind " << op.kind;
}

/* -------------------------------------------------------------------------- */
/* Rules modulo constant bits                                                 */
/* -------------------------------------------------------------------------- */

namespace {

/*
 * The functions below are the rules for a domain x with fixed bits. The
 * callers handle the domains without fixed bits with the base rules above.
 *
 * The conditions are those of FMCAD'20 Tables II-III (invertibility, IC) and
 * IV-V (consistency, CC), with the erratum for x <u s; the values are those
 * of FMSD'17 Tables 2-4 restricted to the values that match x. Every value
 * that the rules can return for a given x, t and ch has a non-zero
 * probability (plan, Sec. 0.5). Where a value is built by setting some bits
 * and drawing the others, x.apply forces the fixed bits of x, which the
 * condition guarantees to agree with the bits that were set.
 */

/** The constant 1 or 0 of width 1. */
const LsValue& boolValue(bool b)
{
  static const LsValue kTrue = mkBool(true);
  static const LsValue kFalse = mkBool(false);
  return b ? kTrue : kFalse;
}

/** The domain of v << k (left) or v >> k (not left) for v matching x. */
TernaryDomain shiftDomain(const TernaryDomain& x, uint32_t k, bool left)
{
  return left ? shlD(x, k) : lshrD(x, k);
}

/**
 * The domain of v >>a k for v matching x: that of v >> k (of ~(~v >> k) if
 * the sign is fixed to 1), and if the sign is free, free copies of it on top.
 * This is exact.
 */
TernaryDomain ashrDomain(const TernaryDomain& x, uint32_t k)
{
  uint32_t w = x.getSize();
  uint32_t m = w - 1;
  if (x.isFixedBit(m))
  {
    return x.isFixedTrue(m) ? notD(lshrD(notD(x), k)) : lshrD(x, k);
  }
  if (k == 0)
  {
    return x;
  }
  if (k >= w)
  {
    return TernaryDomain::full(w);
  }
  return concatD(TernaryDomain::full(k), extractD(x, m, k));
}

/**
 * Return y * t + y - 1, capped at ones: the largest x with x / y = t, for y
 * >= 1 such that y * t does not overflow. The x with x / y = t are the
 * "dividends" [y * t, udivDividendsEnd(y, t)].
 */
LsValue udivDividendsEnd(const LsValue& y, const LsValue& t)
{
  LsValue yt = y * t;
  LsValue d = dec(y);
  return uaddOverflow(yt, d) ? LsValue::mkOnes(t.getSize()) : yt + d;
}

/**
 * The consistent value of x * s = t modulo constant bits (Table V): for t =
 * 0 every value (s = 0); otherwise the values with a 1 at some bit i <=
 * ctz(t), i.e., with ctz(x) <= ctz(t), since x = x' * 2^ctz(x) with x' odd
 * and s = (t >> ctz(x)) / x' give x * s = t.
 */
std::optional<LsValue> mulConsistent(const TernaryDomain& x,
                                     const LsValue& t,
                                     LsRng& rng)
{
  uint32_t w = t.getSize();
  if (isZero(t))
  {
    return pick(x, rng);
  }
  LsValue low = LsValue::mkOnes(w).logicalRightShift(w - 1 - ctz(t));
  LsValue canBeOne = x.hi() & low;
  if (isZero(canBeOne))
  {
    return std::nullopt;
  }
  LsValue v = pick(x, rng);
  if (isZero(v & low))
  {
    // A fixed 1 at a bit <= ctz(t) would be in v, so the bits there that
    // can be 1 are free: set one of them, chosen uniformly. Every
    // consistent value is also drawn directly by pick.
    uint32_t j = rng.pickIndex(popcount(canBeOne));
    for (uint32_t i = 0;; ++i)
    {
      if (canBeOne.isBitSet(i) && j-- == 0)
      {
        return v | LsValue::mkOne(w).leftShift(i);
      }
    }
  }
  return v;
}

/**
 * The consistent value of x / s = t modulo constant bits (plan, Sec. 3.4).
 *
 * For 1 < t < ones, x is consistent iff x / y = t for some y >= 1, i.e., x
 * is a dividend of y: x = t (y = 1), or x >= 2t with x mod t < x div t (y =
 * x div t). The dividends of y >= t cover [t * t, ones]. Table V states this
 * as an existential over y; it is decided in stages, of which only the
 * bounded search of stage 4 can miss a value. A miss there is not
 * systematic: stage 2 draws every consistent value other than t with a
 * non-zero probability, so the search never loses a value for ever (R2).
 */
std::optional<LsValue> udivConsistent(const TernaryDomain& x,
                                      const LsValue& t,
                                      LsRng& rng)
{
  uint32_t w = t.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue one = LsValue::mkOne(w);
  LsValue ones = LsValue::mkOnes(w);
  if (isOnes(t))
  {
    return pick(x, rng);  // x / 0 = ones
  }
  if (isZero(t))
  {
    // Table V: x^lo != ones; x / y = 0 for every y > x.
    if (isOnes(x.lo()))
    {
      return std::nullopt;
    }
    return pick(x, zero, dec(ones), rng);
  }
  if (t == one)
  {
    // x / x = 1 for x != 0.
    if (isZero(x.hi()))
    {
      return std::nullopt;
    }
    return pick(x, one, ones, rng);
  }
  // Table V: x^hi >= t, since every consistent value is at least t.
  if (x.hi().unsignedLessThan(t))
  {
    return std::nullopt;
  }

  // 1. t itself, which the other stages never draw.
  bool tMatches = x.matches(t);
  if (tMatches && rng.pickWithProb(kProbUdivConsT))
  {
    return t;
  }

  // 2. Random divisors y >= 2 whose dividends may lie in [x^lo, x^hi], as in
  // Bitwuzla. Every consistent value v != t is a dividend of y = v div t,
  // which is in this range of y.
  LsValue two = inc(one);
  LsValue ymin = x.lo().unsignedDivTotal(t);
  if (ymin.unsignedLessThan(two))
  {
    ymin = two;
  }
  LsValue ymax = x.hi().unsignedDivTotal(t);
  if (ymin.unsignedLessThanEq(ymax))
  {
    for (uint32_t i = 0; i < kUdivConsTries; ++i)
    {
      LsValue y = rng.randomInRange(ymin, ymax);
      DomainSampler sampler(x, y * t, udivDividendsEnd(y, t));
      if (!sampler.empty())
      {
        return sampler.random(rng);
      }
    }
  }

  // 3. [t * t, ones], where every value is consistent: exact.
  bool squareFits = !umulOverflow(t, t);
  if (squareFits)
  {
    DomainSampler sampler(x, t * t, ones);
    if (!sampler.empty())
    {
      return sampler.random(rng);
    }
  }

  // 4. The smallest consistent matching value in [2t, t * t), jumping from
  // each matching value that falls between two runs of dividends to the next
  // run. Exact if it ends within kSearchLimit steps.
  if (!uaddOverflow(t, t))
  {
    LsValue a = t + t;
    if (a.unsignedLessThan(x.lo()))
    {
      a = x.lo();
    }
    for (uint32_t i = 0; i < kSearchLimit; ++i)
    {
      std::optional<LsValue> v = minMatchingGeq(x, a);
      if (!v)
      {
        break;  // no matching value >= a
      }
      // A matching value >= t * t would have been found in stage 3.
      Assert(!squareFits || v->unsignedLessThan(t * t));
      LsValue y = v->unsignedDivTotal(t);
      if (v->unsignedRemTotal(t).unsignedLessThan(y))
      {
        return DomainSampler(x, y * t, udivDividendsEnd(y, t)).random(rng);
      }
      // v lies after the dividends of y; those of y + 1 start at (y + 1) t.
      if (umulOverflow(inc(y), t))
      {
        break;
      }
      a = inc(y) * t;
    }
  }

  // 5. t, or no value.
  if (tMatches)
  {
    return t;
  }
  return std::nullopt;
}

/**
 * For s mod x = t with n = s - t > t: call f(d) for each divisor d > t of n
 * that matches x and that the bounded search finds, i.e., n itself and the
 * divisor pairs (i, n / i) for i <= kSearchLimit, in a fixed order, until f
 * returns true. Return true iff f did. There is no factorization (plan D19):
 * a divisor d with d > kSearchLimit and n / d > kSearchLimit is not found.
 */
template <class F>
bool forEachFoundDivisor(const TernaryDomain& x,
                         const LsValue& n,
                         const LsValue& t,
                         F f)
{
  uint32_t w = n.getSize();
  auto visit = [&](const LsValue& d) {
    return t.unsignedLessThan(d) && x.matches(d) && f(d);
  };
  for (uint32_t i = 1; i <= kSearchLimit; ++i)
  {
    if (w < 32 && i >= (uint32_t(1) << w))
    {
      break;  // i does not fit in w bits
    }
    LsValue d(w, i);
    if (umulOverflow(d, d) || n.unsignedLessThan(d * d))
    {
      break;  // all pairs seen: i > sqrt(n)
    }
    if (!isZero(n.unsignedRemTotal(d)))
    {
      continue;
    }
    LsValue e = n.unsignedDivTotal(d);
    if (visit(d) || (e != d && visit(e)))
    {
      return true;
    }
  }
  return false;
}

/** Return true if v < k as unsigned integers, whatever the width of v. */
bool lessThan(const LsValue& v, uint32_t k)
{
  uint32_t w = v.getSize();
  if (w < 32 && (uint64_t(1) << w) <= k)
  {
    return true;  // every value of width w is below k
  }
  return v.unsignedLessThan(LsValue(w, k));
}

/**
 * For x mod s = t with s != 0 and t < s, whose solutions are s * k + t for k =
 * 0, ..., (ones - t) / s: return the range [klo, khi] of the multipliers k
 * whose solution lies in [x^lo, x^hi], or nothing if it is empty. s * k + t
 * does not overflow for k <= khi.
 */
std::optional<std::pair<LsValue, LsValue>> uremMultipliers(
    const TernaryDomain& x, const LsValue& s, const LsValue& t)
{
  if (x.hi().unsignedLessThan(t))
  {
    return std::nullopt;
  }
  LsValue khi = (x.hi() - t).unsignedDivTotal(s);
  // klo = ceil((x^lo - t) / s) if x^lo > t, else 0.
  LsValue klo = LsValue::mkZero(t.getSize());
  if (t.unsignedLessThan(x.lo()))
  {
    klo = inc(dec(x.lo() - t).unsignedDivTotal(s));
  }
  if (khi.unsignedLessThan(klo))
  {
    return std::nullopt;
  }
  return std::make_pair(klo, khi);
}

/**
 * For x mod s = t as in uremMultipliers: return the smallest solution s * k +
 * t that matches x with k in [k, khi], trying at most kSearchLimit
 * candidates. From a candidate that does not match, the search jumps to the
 * first multiplier whose solution is at least the next matching value, so it
 * skips the values that x excludes. Nothing if there is no such solution, or
 * if the search runs out of steps, which may then miss one.
 */
std::optional<LsValue> uremFirstSolution(const TernaryDomain& x,
                                         const LsValue& s,
                                         const LsValue& t,
                                         LsValue k,
                                         const LsValue& khi)
{
  for (uint32_t i = 0; i < kSearchLimit; ++i)
  {
    LsValue v = s * k + t;
    std::optional<LsValue> m = minMatchingGeq(x, v);
    if (!m)
    {
      return std::nullopt;  // no matching value >= v
    }
    if (*m == v)
    {
      return v;
    }
    // The first multiplier whose solution is at least m: ceil((m - t) / s).
    k = inc(dec(*m - t).unsignedDivTotal(s));
    if (khi.unsignedLessThan(k))
    {
      return std::nullopt;
    }
  }
  return std::nullopt;
}

/**
 * The part of the invertibility condition that concerns the fixed bits of x.
 * Requires the base condition isInvertible(op, posX, t, ch) to hold.
 */
bool icFixedBits(const OpInfo& op,
                 uint32_t posX,
                 const LsValue& t,
                 const LsChildren& ch,
                 const TernaryDomain& x)
{
  switch (op.kind)
  {
    // ~x = t: Table III, mcb(x, ~t).
    case LsKind::NOT: return x.matches(~t);
    case LsKind::AND:
    {
      // x & s = t: Table III, the base condition (t & s) = t and
      // ((s & x^hi) & c) = (t & c) for the fixed bits c of x: where s is 1, x
      // must equal t, so a fixed bit of x there must be the bit of t.
      const LsValue& s = *ch[1 - posX];
      LsValue fixed = ~x.freeMask();
      return ((s & x.hi()) & fixed) == (t & fixed);
    }
    case LsKind::EQ:
    {
      // (x = s) = t: Table II, (t => mcb(x, s)) and (not t => x is not fixed
      // to s).
      const LsValue& s = *ch[1 - posX];
      return t.isBitSet(0) ? x.matches(s) : !(x.isFixed() && x.lo() == s);
    }
    // x + s = t: Table III, mcb(x, t - s).
    case LsKind::ADD: return x.matches(t - *ch[1 - posX]);
    // x ^ s = t: Table III, mcb(x, s ^ t).
    case LsKind::XOR: return x.matches(t ^ *ch[1 - posX]);
    // x o s = t, s o x = t: Table III, the base condition (s is the rest of
    // t) and mcb(x, the part of t for x).
    case LsKind::CONCAT: return x.matches(concatPartOf(posX, t, ch));
    // x[u:l] = t: Table III, mcb(x[u:l], t).
    case LsKind::EXTRACT: return extractD(x, op.hi, op.lo).matches(t);
    // sext(x) = t: Table III, the base condition (the top n + 1 bits of t are
    // all 0 or all 1) and mcb(x, the low w bits of t).
    case LsKind::SEXT: return x.matches(t.extract(x.getSize() - 1, 0));
    case LsKind::ASHR:
    {
      if (posX == 0)
      {
        // x >>a s = t: Table III, the base condition and mcb(x >>a s, t), with
        // the exact domain of x >>a s.
        return ashrDomain(x, shiftAmount(*ch[1], t.getSize())).matches(t);
      }
      // s >>a x = t: Table III, the condition of s' >> x = t'.
      auto [s, tl] = ashrAsLshr(*ch[0], t);
      LsChildren chl{&s, ch[1]};
      return icFixedBits({LsKind::LSHR}, 1, tl, chl, x);
    }
    case LsKind::ITE:
      // Not in the paper (plan D16). For the condition, a branch equal to t
      // whose selecting value matches x; for a branch, it must be enabled
      // (the base condition) and t must match x.
      if (posX == 0)
      {
        return (*ch[1] == t && x.matches(boolValue(true)))
               || (*ch[2] == t && x.matches(boolValue(false)));
      }
      return x.matches(t);
    case LsKind::ULT:
    {
      // Table II with the erratum: (x <u s) = t needs, for t, a matching
      // value below s (the base condition gives s != 0), and for not t, one
      // at least s; lo is the smallest and hi the largest matching value.
      // (s <u x) = t is symmetric.
      const LsValue& s = *ch[1 - posX];
      bool lt = t.isBitSet(0);
      if (posX == 0)
      {
        return lt ? x.lo().unsignedLessThan(s) : !x.hi().unsignedLessThan(s);
      }
      return lt ? s.unsignedLessThan(x.hi()) : x.lo().unsignedLessThanEq(s);
    }
    case LsKind::SHL:
    case LsKind::LSHR:
    {
      bool left = op.kind == LsKind::SHL;
      uint32_t w = t.getSize();
      if (posX == 0)
      {
        // x << s = t: Table III, mcb(x << s, t), with the exact domain of
        // x << s.
        return shiftDomain(x, shiftAmount(*ch[1], w), left).matches(t);
      }
      // s << x = t: Table III. For t != 0 the base condition fixes the
      // amount to zeros(t) - zeros(s), which x must match. For t = 0 either
      // s = 0, or the amount shifts all set bits of s out: it is at least
      // w - zeros(s), and hi is the largest matching value.
      const LsValue& s = *ch[0];
      if (isZero(t))
      {
        return isZero(s)
               || !x.hi().unsignedLessThan(LsValue(w, w - shiftZeros(s, left)));
      }
      return x.matches(LsValue(w, shiftZeros(t, left) - shiftZeros(s, left)));
    }
    case LsKind::MUL:
    {
      // x * s = t: Table III. If s = 0 then t = 0 (the base condition) and
      // every x is a solution. Otherwise, with c = ctz(s) and y = (t >> c) *
      // (s >> c)^-1, the solutions are the values whose low w - c bits are
      // those of y: mcb(x << c, y << c).
      const LsValue& s = *ch[1 - posX];
      if (isZero(s))
      {
        return true;
      }
      uint32_t c = ctz(s);
      LsValue y = t.logicalRightShift(c) * modInverse(s.logicalRightShift(c));
      return shlD(x, c).matches(y.leftShift(c));
    }
    case LsKind::UDIV:
    {
      // Table III gives these conditions as existentials; the solutions form
      // an interval, so they are decided exactly.
      const LsValue& s = *ch[1 - posX];
      uint32_t w = t.getSize();
      if (posX == 0)
      {
        // x / s = t: the dividends of s (s * t does not overflow by the base
        // condition); s = 0 needs t = ones, and then every x works.
        return isZero(s) || hasMatchingIn(x, s * t, udivDividendsEnd(s, t));
      }
      // s / x = t: for t = ones, x = 0, or x = 1 if s = ones; otherwise x in
      // [s / (t + 1) + 1, s / t].
      if (isOnes(t))
      {
        return x.matches(LsValue::mkZero(w))
               || (isOnes(s) && x.matches(LsValue::mkOne(w)));
      }
      return hasMatchingIn(
          x, inc(s.unsignedDivTotal(inc(t))), s.unsignedDivTotal(t));
    }
    case LsKind::UREM:
    {
      if (posX == 0)
      {
        // x mod s = t: Table III. The base condition gives s = 0 or t < s.
        // For s = 0 (x mod 0 = x) the only solution is t. Otherwise the
        // existential asks for a multiplier k with s * k + t matching x; it
        // is decided in stages, of which only the last is bounded.
        const LsValue& s = *ch[1];
        if (isZero(s))
        {
          return x.matches(t);
        }
        // Every solution has the low ctz(s) bits of t: exact no.
        uint32_t c = ctz(s);
        if (c > 0 && !extractD(x, c - 1, 0).matches(t.extract(c - 1, 0)))
        {
          return false;
        }
        // s = 2^c: every value with those low bits is a solution: exact yes.
        if (popcount(s) == 1)
        {
          return true;
        }
        // No multiplier puts the solution in [x^lo, x^hi]: exact no. Else
        // the search, exact if it ends within kSearchLimit steps. A wrong no
        // only sends the step to tryConsistentValue, whose values include
        // every inverse value.
        std::optional<std::pair<LsValue, LsValue>> range =
            uremMultipliers(x, s, t);
        return range
               && uremFirstSolution(x, s, t, range->first, range->second)
                      .has_value();
      }
      // s mod x = t: Table III. The base condition holds, so s >= t.
      const LsValue& s = *ch[0];
      uint32_t w = t.getSize();
      if (s == t)
      {
        // (x^lo = 0 or x^hi > t): s mod 0 = s, and s mod x = s for x > s.
        return x.matches(LsValue::mkZero(w)) || t.unsignedLessThan(x.hi());
      }
      // The existential of Table III: a divisor y > t of n = s - t that
      // matches x (the base condition gives n > t). First the exact tests:
      // a divisor is at most n, and has at most ctz(n) trailing zeros, so
      // one of the bits 0, ..., ctz(n) of x must be able to be 1.
      LsValue n = s - t;
      if (!hasMatchingIn(x, inc(t), n))
      {
        return false;
      }
      LsValue low = LsValue::mkOnes(w).logicalRightShift(w - 1 - ctz(n));
      if (isZero(x.hi() & low))
      {
        return false;
      }
      // Then the bounded search, without factorization (plan D19): it may
      // say no although a divisor matches, never the opposite. A wrong no
      // only sends the step to tryConsistentValue, whose values include
      // every inverse value.
      return forEachFoundDivisor(x, n, t, [](const LsValue&) { return true; });
    }
    case LsKind::CONST:
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "isInvertible called on leaf kind " << op.kind;
}

/** The inverse value rules, see inverseValue. Requires icFixedBits. */
LsValue inverseFixedBits(const OpInfo& op,
                         uint32_t posX,
                         const LsValue& t,
                         const LsChildren& ch,
                         const TernaryDomain& x,
                         LsRng& rng)
{
  uint32_t w = x.getSize();
  switch (op.kind)
  {
    case LsKind::NOT: return ~t;
    case LsKind::AND:
      // Where s is 1, the bit of t; elsewhere any bit that matches x.
      return x.apply(t | (rng.randomValue(w) & ~*ch[1 - posX]));
    case LsKind::EQ:
    {
      const LsValue& s = *ch[1 - posX];
      return t.isBitSet(0) ? s : pickNotEqual(x, s, rng);
    }
    case LsKind::ADD: return t - *ch[1 - posX];
    case LsKind::XOR: return t ^ *ch[1 - posX];
    case LsKind::SEXT: return t.extract(w - 1, 0);
    case LsKind::ASHR:
    {
      if (posX == 0)
      {
        // The bits of x that survive the shift come from t and match x; the
        // others are drawn and then forced to the fixed bits of x.
        return x.apply(invAshrValue(shiftAmount(*ch[1], w), t, rng));
      }
      auto [s, tl] = ashrAsLshr(*ch[0], t);
      LsChildren chl{&s, ch[1]};
      return inverseFixedBits({LsKind::LSHR}, 1, tl, chl, x, rng);
    }
    case LsKind::CONCAT: return concatPartOf(posX, t, ch);
    case LsKind::EXTRACT:
      // The base rule (the bits outside [u:l] kept, drawn, or set to all 0s
      // or all 1s) with the fixed bits forced in; the slice is t, which
      // matches x there.
      return x.apply(computeInverse(op, posX, t, ch, rng));
    case LsKind::ITE:
    {
      if (posX > 0)
      {
        return t;
      }
      // A condition that selects a branch equal to t; x is fixed here, since
      // a domain of width 1 with a fixed bit has a single value.
      bool a = *ch[1] == t && x.matches(boolValue(true));
      bool b = *ch[2] == t && x.matches(boolValue(false));
      return a && b ? rng.randomValue(1) : boolValue(a);
    }
    case LsKind::ULT:
    {
      // The base ranges (FMSD'17 Table 3), drawn among the matching values.
      const LsValue& s = *ch[1 - posX];
      LsValue zero = LsValue::mkZero(w);
      LsValue ones = LsValue::mkOnes(w);
      bool lt = t.isBitSet(0);
      if (posX == 0)
      {
        return lt ? pick(x, zero, dec(s), rng) : pick(x, s, ones, rng);
      }
      return lt ? pick(x, inc(s), ones, rng) : pick(x, zero, s, rng);
    }
    case LsKind::SHL:
    case LsKind::LSHR:
    {
      bool left = op.kind == LsKind::SHL;
      if (posX == 0)
      {
        // The bits of x that survive the shift are those of t shifted back,
        // which match x; the bits shifted out are drawn and then forced to
        // the fixed bits of x.
        return x.apply(invShift(posX, t, ch, left, rng));
      }
      const LsValue& s = *ch[0];
      if (!isZero(t))
      {
        return LsValue(w, shiftZeros(t, left) - shiftZeros(s, left));
      }
      if (isZero(s))
      {
        return pick(x, rng);
      }
      return pick(
          x, LsValue(w, w - shiftZeros(s, left)), LsValue::mkOnes(w), rng);
    }
    case LsKind::MUL:
    {
      const LsValue& s = *ch[1 - posX];
      if (isZero(s))
      {
        return pick(x, rng);
      }
      // The low w - c bits from y, which match x; the top c bits are drawn
      // and then forced to the fixed bits of x.
      return x.apply(invMul(s, t, rng));
    }
    case LsKind::UDIV:
    {
      const LsValue& s = *ch[1 - posX];
      if (posX == 0)
      {
        if (isZero(s))
        {
          return pick(x, rng);
        }
        // The smallest dividend with the probability of the base rule.
        LsValue lo = s * t;
        if (rng.pickWithProb(kProbUdivLo) && x.matches(lo))
        {
          return lo;
        }
        return pick(x, lo, udivDividendsEnd(s, t), rng);
      }
      if (isOnes(t))
      {
        LsValue zero = LsValue::mkZero(w);
        LsValue one = LsValue::mkOne(w);
        bool z = x.matches(zero);
        bool o = isOnes(s) && x.matches(one);
        if (z && o)
        {
          return rng.randomInRange(zero, one);
        }
        return z ? zero : one;
      }
      return pick(
          x, inc(s.unsignedDivTotal(inc(t))), s.unsignedDivTotal(t), rng);
    }
    case LsKind::UREM:
    {
      if (posX == 0)
      {
        const LsValue& s = *ch[1];
        if (isZero(s))
        {
          return t;
        }
        uint32_t c = ctz(s);
        if (popcount(s) == 1)
        {
          // Every value with the low c bits of t: draw the others.
          LsValue v = pick(x, rng);
          return c == 0 ? v : setSlice(v, c - 1, 0, t.extract(c - 1, 0));
        }
        std::optional<std::pair<LsValue, LsValue>> range =
            uremMultipliers(x, s, t);
        Assert(range);
        const auto& [klo, khi] = *range;
        if (lessThan(khi - klo, kSearchLimit))
        {
          // Few multipliers: a uniform solution among all of them.
          uint32_t count = 0;
          for (LsValue k = klo;; k = inc(k))
          {
            count += x.matches(s * k + t);
            if (k == khi)
            {
              break;
            }
          }
          Assert(count > 0);
          uint32_t j = rng.pickIndex(count);
          for (LsValue k = klo;; k = inc(k))
          {
            LsValue v = s * k + t;
            if (x.matches(v) && j-- == 0)
            {
              return v;
            }
          }
        }
        // Uniform multipliers, so that every solution has a non-zero
        // probability, then the first solution, which isInvertible found.
        for (uint32_t i = 0; i < kUremMultiplierTries; ++i)
        {
          LsValue v = s * rng.randomInRange(klo, khi) + t;
          if (x.matches(v))
          {
            return v;
          }
        }
        std::optional<LsValue> v = uremFirstSolution(x, s, t, klo, khi);
        Assert(v);
        return *v;
      }
      const LsValue& s = *ch[0];
      LsValue zero = LsValue::mkZero(w);
      if (s == t)
      {
        // 0, with the probability of the base rule, or any value > t.
        bool zeroOk = x.matches(zero);
        bool aboveOk = t.unsignedLessThan(x.hi());
        if (zeroOk && (!aboveOk || rng.pickWithProb(kProbUremInvZero)))
        {
          return zero;
        }
        return pick(x, inc(t), LsValue::mkOnes(w), rng);
      }
      LsValue n = s - t;
      // The choices of the base rule: n itself, and 1 for t = 0.
      if (x.matches(n) && rng.pickWithProb(kProbUremInvN))
      {
        return n;
      }
      LsValue one = LsValue::mkOne(w);
      if (isZero(t) && x.matches(one) && rng.pickWithProb(kProbUremInvOne))
      {
        return one;
      }
      // Sometimes, values of (t, n] that match x, kept if they divide n: every
      // divisor that matches x has a non-zero probability, including those
      // the bounded search misses (plan R3, D19).
      if (rng.pickWithProb(kProbUremInvSample))
      {
        DomainSampler sampler(x, inc(t), n);
        Assert(!sampler.empty());
        for (uint32_t i = 0; i < kUremDivisorSamples; ++i)
        {
          LsValue d = sampler.random(rng);
          if (isZero(n.unsignedRemTotal(d)))
          {
            return d;
          }
        }
      }
      // Otherwise a uniform divisor among those the bounded search finds;
      // isInvertible found one.
      uint32_t count = 0;
      forEachFoundDivisor(x, n, t, [&count](const LsValue&) {
        ++count;
        return false;
      });
      Assert(count > 0);
      uint32_t j = rng.pickIndex(count);
      LsValue res;
      forEachFoundDivisor(x, n, t, [&j, &res](const LsValue& d) {
        if (j-- > 0)
        {
          return false;
        }
        res = d;
        return true;
      });
      return res;
    }
    case LsKind::CONST:
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "inverseValue called on leaf kind " << op.kind;
}

/**
 * The consistency condition and the consistent value rules, see
 * tryConsistentValue.
 */
std::optional<LsValue> consistentFixedBits(const OpInfo& op,
                                           uint32_t posX,
                                           const LsValue& t,
                                           const LsChildren& ch,
                                           const TernaryDomain& x,
                                           LsRng& rng)
{
  uint32_t w = x.getSize();
  switch (op.kind)
  {
    case LsKind::NOT:
    {
      // Table V: mcb(x, ~t); ~t is the only consistent value.
      LsValue v = ~t;
      return x.matches(v) ? std::optional<LsValue>(v) : std::nullopt;
    }
    case LsKind::AND:
      // Table V: (t & x^hi) = t, i.e., x can be 1 wherever t is; the
      // consistent values are those with a 1 wherever t has one.
      if ((t & x.hi()) != t)
      {
        return std::nullopt;
      }
      return x.apply(t | rng.randomValue(w));
    case LsKind::EQ:
    case LsKind::ADD:
    case LsKind::XOR:
      // Tables IV-V: true; every value is consistent.
      return pick(x, rng);
    case LsKind::CONCAT:
    {
      // Table V: mcb(x, the part of t for x), the only consistent value.
      LsValue v = concatPartOf(posX, t, ch);
      return x.matches(v) ? std::optional<LsValue>(v) : std::nullopt;
    }
    case LsKind::EXTRACT:
      // Table V: the IC, mcb(x[u:l], t); the bits outside [u:l] are free.
      if (!extractD(x, op.hi, op.lo).matches(t))
      {
        return std::nullopt;
      }
      return x.apply(setSlice(rng.randomValue(w), op.hi, op.lo, t));
    case LsKind::SEXT:
    {
      // Table V: the IC (unary); the low w bits of t are the only value.
      LsValue v = t.extract(w - 1, 0);
      return isSignExtension(t, w) && x.matches(v) ? std::optional<LsValue>(v)
                                                   : std::nullopt;
    }
    case LsKind::ASHR:
    {
      bool constant = isZero(t) || isOnes(t);
      if (posX == 1)
      {
        // s' >>a x = t: Table V, t in {0, ones} (every amount), or an amount
        // below signRun(t) that matches x.
        if (constant)
        {
          return pick(x, rng);
        }
        LsValue maxAmount(w, signRun(t) - 1);
        if (!hasMatchingIn(x, LsValue::mkZero(w), maxAmount))
        {
          return std::nullopt;
        }
        return pick(x, LsValue::mkZero(w), maxAmount, rng);
      }
      uint32_t m = w - 1;
      if (constant)
      {
        // x >>a s' = t: Table V, for t in {0, ones} some value matching x
        // with the sign of t; every such value is consistent.
        if (x.isFixedBit(m) && x.isFixedTrue(m) != msb(t))
        {
          return std::nullopt;
        }
        return x.apply(invAshrValue(w, t, rng));
      }
      // Otherwise Table V: some amount k < signRun(t) with mcb(x >>a k, t).
      // Draw such an amount uniformly, then a value as the inverse value for
      // it, so that every consistent value has a non-zero probability.
      uint32_t run = signRun(t);
      uint32_t n = 0;
      for (uint32_t k = 0; k < run; ++k)
      {
        n += ashrDomain(x, k).matches(t);
      }
      if (n == 0)
      {
        return std::nullopt;
      }
      uint32_t j = rng.pickIndex(n);
      uint32_t k = 0;
      for (;; ++k)
      {
        if (ashrDomain(x, k).matches(t) && j-- == 0)
        {
          break;
        }
      }
      return x.apply(invAshrValue(k, t, rng));
    }
    case LsKind::ITE:
      // Not in the paper (plan D16). Every condition is consistent. For a
      // branch the consistent value is t, if it matches x, as in the base
      // rule; otherwise the move ends in a conflict (plan D11).
      if (posX == 0)
      {
        return pick(x, rng);
      }
      return x.matches(t) ? std::optional<LsValue>(t) : std::nullopt;
    case LsKind::ULT:
    {
      // Table IV: not t, or x^lo != ones (x <u s'), or x^hi != 0 (s' <u x).
      if (!t.isBitSet(0))
      {
        return pick(x, rng);
      }
      LsValue zero = LsValue::mkZero(w);
      LsValue ones = LsValue::mkOnes(w);
      if (posX == 0)
      {
        if (isOnes(x.lo()))
        {
          return std::nullopt;
        }
        return pick(x, zero, dec(ones), rng);
      }
      if (isZero(x.hi()))
      {
        return std::nullopt;
      }
      return pick(x, LsValue::mkOne(w), ones, rng);
    }
    case LsKind::SHL:
    case LsKind::LSHR:
    {
      // Every value is consistent with t = 0: shift by w, or shift 0.
      if (isZero(t))
      {
        return pick(x, rng);
      }
      bool left = op.kind == LsKind::SHL;
      uint32_t zt = shiftZeros(t, left);
      if (posX == 0)
      {
        // Table V: some amount k <= zeros(t) with mcb(x << k, t). Draw such
        // an amount uniformly, then a value as the inverse value for it, so
        // that every consistent value has a non-zero probability.
        uint32_t n = 0;
        for (uint32_t k = 0; k <= zt; ++k)
        {
          n += shiftDomain(x, k, left).matches(t);
        }
        if (n == 0)
        {
          return std::nullopt;
        }
        uint32_t j = rng.pickIndex(n);
        uint32_t k = 0;
        for (;; ++k)
        {
          if (shiftDomain(x, k, left).matches(t) && j-- == 0)
          {
            break;
          }
        }
        return x.apply(randomizeLostBits(shiftBy(t, k, !left), k, left, rng));
      }
      // Table V (synthesized), equivalently x^lo <= zeros(t): the amounts
      // that keep the bits of t are 0, ..., zeros(t).
      LsValue maxAmount(w, zt);
      if (maxAmount.unsignedLessThan(x.lo()))
      {
        return std::nullopt;
      }
      return pick(x, LsValue::mkZero(w), maxAmount, rng);
    }
    case LsKind::MUL: return mulConsistent(x, t, rng);
    case LsKind::UDIV:
    {
      if (posX == 0)
      {
        return udivConsistent(x, t, rng);
      }
      // s' / x = t: Table V. For t = ones, x in {0, 1} (s' / 0, ones / 1);
      // otherwise x in [1, ones / t], those with x * t <= ones (s' = x * t).
      LsValue one = LsValue::mkOne(w);
      DomainSampler sampler =
          isOnes(t)
              ? DomainSampler(x, LsValue::mkZero(w), one)
              : DomainSampler(x, one, LsValue::mkOnes(w).unsignedDivTotal(t));
      if (sampler.empty())
      {
        return std::nullopt;
      }
      return sampler.random(rng);
    }
    case LsKind::UREM:
    {
      if (posX == 0)
      {
        // x mod s' = t: Table V. The consistent values are t (s' = 0) and,
        // if 2t + 1 does not overflow, every x > 2t (s' = x - t > t).
        bool tOk = x.matches(t);
        bool aboveOk = !isOnes(t) && !uaddOverflow(t, inc(t))
                       && !x.hi().unsignedLessThan(t + inc(t));
        if (!tOk && !aboveOk)
        {
          return std::nullopt;
        }
        if (tOk && (!aboveOk || rng.pickWithProb(kProbUremConsT)))
        {
          return t;
        }
        return pick(x, t + inc(t), LsValue::mkOnes(w), rng);
      }
      // s' mod x = t: Table V (synthesized), equivalently x^lo = 0 or x^hi >
      // t. The consistent values are 0 (s' = t) and every x > t (s' = t), as
      // in the base rule.
      LsValue zero = LsValue::mkZero(w);
      bool zeroOk = x.matches(zero);
      bool aboveOk = t.unsignedLessThan(x.hi());
      if (!zeroOk && !aboveOk)
      {
        return std::nullopt;
      }
      if (zeroOk && (!aboveOk || rng.pickWithProb(kProbUremConsZero)))
      {
        return zero;
      }
      return pick(x, inc(t), LsValue::mkOnes(w), rng);
    }
    case LsKind::CONST:
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "tryConsistentValue called on leaf kind " << op.kind;
}

}  // namespace

bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const LsChildren& ch,
                  const TernaryDomain& x)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    return isInvertible(kUltOp, posX, t, f.get(), flipMsbD(x));
  }
  Assert(x.getSize() == ch[posX]->getSize());
  // Every condition modulo constant bits includes the base condition.
  if (!isInvertible(op, posX, t, ch))
  {
    return false;
  }
  return !x.hasFixedBits() || icFixedBits(op, posX, t, ch, x);
}

bool isEssential(const OpInfo& op,
                 uint32_t i,
                 const LsValue& t,
                 const LsChildren& ch,
                 const LsDomains& doms)
{
  Assert(ch.size() == arity(op.kind));
  Assert(doms.size() == ch.size());
  Assert(i < ch.size());
  for (uint32_t j = 0, n = ch.size(); j < n; ++j)
  {
    if (j != i && !doms[j]->isFixed() && isInvertible(op, j, t, ch, *doms[j]))
    {
      return false;
    }
  }
  return true;
}

LsValue inverseValue(const OpInfo& op,
                     uint32_t posX,
                     const LsValue& t,
                     const LsChildren& ch,
                     const TernaryDomain& x,
                     LsRng& rng)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    return flipMsb(inverseValue(kUltOp, posX, t, f.get(), flipMsbD(x), rng));
  }
  if (!x.hasFixedBits())
  {
    return inverseValue(op, posX, t, ch, rng);
  }
  Assert(x.matches(*ch[posX]))
      << "current value " << *ch[posX] << " does not match " << x;
  Assert(isInvertible(op, posX, t, ch, x));
  LsValue v = inverseFixedBits(op, posX, t, ch, x, rng);
#ifdef CVC5_ASSERTIONS
  Assert(x.matches(v)) << "inverse value " << v << " for " << op.kind << " at "
                       << posX << " does not match " << x;
  LsChildren chx = ch;
  chx[posX] = &v;
  Assert(evaluate(op, chx) == t) << "inverse value " << v << " for " << op.kind
                                 << " at " << posX << " does not produce " << t;
#endif
  return v;
}

std::optional<LsValue> tryConsistentValue(const OpInfo& op,
                                          uint32_t posX,
                                          const LsValue& t,
                                          const LsChildren& ch,
                                          const TernaryDomain& x,
                                          LsRng& rng)
{
  if (op.kind == LsKind::SLT)
  {
    FlippedChildren f(ch);
    std::optional<LsValue> v =
        tryConsistentValue(kUltOp, posX, t, f.get(), flipMsbD(x), rng);
    if (v)
    {
      return flipMsb(*v);
    }
    return v;
  }
  Assert(ch.size() == arity(op.kind));
  Assert(posX < ch.size());
  Assert(x.getSize() == ch[posX]->getSize());
  if (op.kind == LsKind::SEXT && !isInvertible(op, posX, t, ch))
  {
    // t is not a sign extension: no value of x is consistent.
    return std::nullopt;
  }
  if (!x.hasFixedBits())
  {
    // For the other base operators a consistent value always exists.
    return consistentValue(op, posX, t, ch, rng);
  }
  Assert(x.matches(*ch[posX]))
      << "current value " << *ch[posX] << " does not match " << x;
  std::optional<LsValue> v = consistentFixedBits(op, posX, t, ch, x, rng);
  Assert(!v || x.matches(*v)) << "consistent value " << *v << " for " << op.kind
                              << " at " << posX << " does not match " << x;
  return v;
}

namespace {

/*
 * The domains of the operators that ls_domain does not provide (plan Sec.
 * 5.2, D23): XOR, and those whose exact domain is not a simple bitwise
 * function of their operands' domains. Each is sound:
 * the value of the operator on any values that match the operands' domains
 * matches it. They are word-level "known bits" rules in the spirit of the
 * word-level propagators that FMCAD'20 Sec. IV-B leaves to future work.
 */

/**
 * Return the domain of the values in [a, b]: their common leading bits are
 * fixed. Requires a <= b.
 */
TernaryDomain intervalD(const LsValue& a, const LsValue& b)
{
  Assert(a.unsignedLessThanEq(b));
  if (a == b)
  {
    return TernaryDomain::fixed(a);
  }
  // a and b agree above their highest differing bit, and so does every
  // value between them.
  LsValue low = LsValue::mkOnes(a.getSize()).logicalRightShift(clz(a ^ b));
  return TernaryDomain(a & ~low, a | low);
}

/**
 * The domain of v + u (LLVM's KnownBits::computeForAddSub). The sum of the
 * largest values x^hi + y^hi has the largest carries and the sum of the
 * smallest x^lo + y^lo the smallest, so a carry is known where it is 0 in
 * the former or 1 in the latter; a bit of the sum is known where both
 * operand bits and the carry into it are known.
 *
 * This is exact. If an operand bit i is free, flipping it flips bit i of the
 * sum and not the carry into it. The carry into bit i is the carry out of the
 * sum of the low i bits, which grows with both operands, so it is the same
 * for all values iff it is the same for the smallest and the largest.
 */
TernaryDomain addD(const TernaryDomain& x, const TernaryDomain& y)
{
  LsValue sumHi = x.hi() + y.hi();
  LsValue sumLo = x.lo() + y.lo();
  LsValue carryKnown = ~(sumHi ^ x.hi() ^ y.hi()) | (sumLo ^ x.lo() ^ y.lo());
  LsValue known = ~x.freeMask() & ~y.freeMask() & carryKnown;
  return TernaryDomain(sumLo & known, sumHi | ~known);
}

/**
 * The domain of v ^ u: a bit is fixed where it is fixed in both operands, to
 * the exclusive or of the two. This is exact: a free operand bit flips the
 * result bit.
 */
TernaryDomain xorD(const TernaryDomain& x, const TernaryDomain& y)
{
  LsValue known = ~x.freeMask() & ~y.freeMask();
  LsValue v = x.lo() ^ y.lo();
  return TernaryDomain(v & known, v | ~known);
}

/**
 * The domain of v sign-extended by n bits: x below the n copies of its most
 * significant bit, fixed if that bit is. This is exact: when the bit is free,
 * each copy takes both values.
 */
TernaryDomain sextD(const TernaryDomain& x, uint32_t n)
{
  uint32_t m = x.getSize() - 1;
  TernaryDomain top = !x.isFixedBit(m) ? TernaryDomain::full(n)
                      : x.isFixedTrue(m)
                          ? TernaryDomain::fixed(LsValue::mkOnes(n))
                          : TernaryDomain::fixed(LsValue::mkZero(n));
  return concatD(top, x);
}

/**
 * The domain of v * u: the product has at least ctz(x^hi) + ctz(y^hi)
 * trailing zeros; its low k bits depend only on the low k bits of the
 * operands, so they are fixed if those are; and if the largest product does
 * not overflow, the product lies in [x^lo * y^lo, x^hi * y^hi].
 */
TernaryDomain mulD(const TernaryDomain& x, const TernaryDomain& y)
{
  uint32_t w = x.getSize();
  uint32_t zeros = std::min(w, ctz(x.hi()) + ctz(y.hi()));
  uint32_t lowFixed = std::min(ctz(x.freeMask()), ctz(y.freeMask()));
  uint32_t k = std::max(zeros, lowFixed);
  LsValue product = x.lo() * y.lo();
  LsValue mask =
      k == 0 ? LsValue::mkZero(w) : LsValue::mkOnes(w).logicalRightShift(w - k);
  TernaryDomain res(product & mask, product | ~mask);
  if (!umulOverflow(x.hi(), y.hi()))
  {
    std::optional<TernaryDomain> m =
        meet(res, intervalD(product, x.hi() * y.hi()));
    Assert(m);
    res = *m;
  }
  return res;
}

/**
 * The domain of v / u (with v / 0 = ones): the quotient lies in [x^lo / y^hi,
 * x^hi / y^lo], or in [x^lo / y^hi, ones] if u can be 0.
 */
TernaryDomain udivD(const TernaryDomain& x, const TernaryDomain& y)
{
  uint32_t w = x.getSize();
  LsValue ones = LsValue::mkOnes(w);
  if (isZero(y.hi()))
  {
    return TernaryDomain::fixed(ones);  // u = 0
  }
  LsValue lb = x.lo().unsignedDivTotal(y.hi());
  LsValue ub = isZero(y.lo()) ? ones : x.hi().unsignedDivTotal(y.lo());
  return intervalD(lb, ub);
}

/**
 * The domain of v mod u (with v mod 0 = v): v itself if v < u always; the
 * low bits of v if u is a fixed power of two; otherwise the remainder is at
 * most x^hi, and below y^hi if u cannot be 0.
 */
TernaryDomain uremD(const TernaryDomain& x, const TernaryDomain& y)
{
  uint32_t w = x.getSize();
  if (x.hi().unsignedLessThan(y.lo()) || (y.isFixed() && isZero(y.lo())))
  {
    return x;
  }
  if (y.isFixed() && popcount(y.lo()) == 1)
  {
    LsValue mask = dec(y.lo());
    return TernaryDomain(x.lo() & mask, x.hi() & mask);
  }
  LsValue ub = x.hi();
  if (!isZero(y.lo()) && dec(y.hi()).unsignedLessThan(ub))
  {
    ub = dec(y.hi());
  }
  return intervalD(LsValue::mkZero(w), ub);
}

/** The domain of v shifted by the constant k, for kind SHL, LSHR or ASHR. */
TernaryDomain shiftByD(const TernaryDomain& x, LsKind kind, uint32_t k)
{
  switch (kind)
  {
    case LsKind::SHL: return shlD(x, k);
    case LsKind::LSHR: return lshrD(x, k);
    default: Assert(kind == LsKind::ASHR); return ashrDomain(x, k);
  }
}

/**
 * The domain of v << u, v >> u or v >>a u (kind SHL, LSHR or ASHR): the join
 * of the exact domains for each shift amount k <= w that u can take (all
 * amounts of w or more shift the same).
 */
TernaryDomain shiftD(const TernaryDomain& x,
                     const TernaryDomain& amount,
                     LsKind kind)
{
  uint32_t w = x.getSize();
  std::optional<TernaryDomain> res;
  for (uint32_t k = 0; k <= w; ++k)
  {
    bool possible =
        k < w ? amount.matches(LsValue(w, k))
              : hasMatchingIn(amount, LsValue(w, w), LsValue::mkOnes(w));
    if (!possible)
    {
      continue;
    }
    TernaryDomain d = shiftByD(x, kind, k);
    res = res ? join(*res, d) : d;
    if (!res->hasFixedBits())
    {
      break;  // it cannot become more precise
    }
  }
  Assert(res);
  return *res;
}

}  // namespace

TernaryDomain forwardDomain(const OpInfo& op, const LsDomains& doms)
{
  if (op.kind == LsKind::SLT)
  {
    TernaryDomain a = flipMsbD(*doms[0]);
    TernaryDomain b = flipMsbD(*doms[1]);
    return forwardDomain(kUltOp, {&a, &b});
  }
  Assert(doms.size() == arity(op.kind));
  // If every child has a single value, so does the operator.
  bool allFixed = true;
  for (uint32_t i = 0, n = doms.size(); i < n; ++i)
  {
    allFixed = allFixed && doms[i]->isFixed();
  }
  if (allFixed)
  {
    LsChildren ch;
    for (uint32_t i = 0, n = doms.size(); i < n; ++i)
    {
      ch.push_back(&doms[i]->lo());
    }
    return TernaryDomain::fixed(evaluate(op, ch));
  }
  const TernaryDomain& x = *doms[0];
  switch (op.kind)
  {
    case LsKind::NOT: return notD(x);
    case LsKind::AND: return andD(x, *doms[1]);
    case LsKind::CONCAT: return concatD(x, *doms[1]);
    case LsKind::EXTRACT: return extractD(x, op.hi, op.lo);
    case LsKind::SEXT: return sextD(x, op.hi);
    case LsKind::SHL:
    case LsKind::LSHR:
    case LsKind::ASHR:
    {
      const TernaryDomain& amount = *doms[1];
      if (amount.isFixed())
      {
        return shiftByD(x, op.kind, shiftAmount(amount.lo(), x.getSize()));
      }
      return shiftD(x, amount, op.kind);
    }
    case LsKind::ITE:
      // The selected branch if the condition is fixed, else either branch.
      if (x.isFixed())
      {
        return x.lo().isBitSet(0) ? *doms[1] : *doms[2];
      }
      return join(*doms[1], *doms[2]);
    case LsKind::EQ:
      // False if no value matches both; true only if both are fixed.
      return meet(x, *doms[1]) ? TernaryDomain::full(1)
                               : TernaryDomain::fixed(LsValue(1, 0u));
    case LsKind::ULT:
    {
      // lo is the smallest and hi the largest matching value.
      const TernaryDomain& y = *doms[1];
      if (x.hi().unsignedLessThan(y.lo()))
      {
        return TernaryDomain::fixed(LsValue(1, 1u));
      }
      if (!x.lo().unsignedLessThan(y.hi()))
      {
        return TernaryDomain::fixed(LsValue(1, 0u));
      }
      return TernaryDomain::full(1);
    }
    case LsKind::ADD: return addD(x, *doms[1]);
    case LsKind::XOR: return xorD(x, *doms[1]);
    case LsKind::MUL: return mulD(x, *doms[1]);
    case LsKind::UDIV: return udivD(x, *doms[1]);
    case LsKind::UREM: return uremD(x, *doms[1]);
    case LsKind::CONST:
    case LsKind::VAR:
    case LsKind::SLT: break;
  }
  Unreachable() << "forwardDomain called on leaf kind " << op.kind;
}

bool isIneqKind(LsKind k) { return k == LsKind::ULT || k == LsKind::SLT; }

std::optional<LsBounds> ineqSolutions(LsKind k,
                                      uint32_t posX,
                                      bool holds,
                                      const LsValue& s)
{
  Assert(isIneqKind(k));
  Assert(posX < 2);
  if (k == LsKind::SLT)
  {
    std::optional<LsBounds> b =
        ineqSolutions(LsKind::ULT, posX, holds, flipMsb(s));
    if (b)
    {
      return LsBounds{flipMsb(b->lo), flipMsb(b->hi)};
    }
    return b;
  }
  uint32_t w = s.getSize();
  LsValue zero = LsValue::mkZero(w);
  LsValue ones = LsValue::mkOnes(w);
  if (posX == 0)
  {
    // x <u s: [0, s - 1], empty for s = 0; x >=u s: [s, ones].
    if (holds)
    {
      return isZero(s) ? std::nullopt
                       : std::optional<LsBounds>(LsBounds{zero, dec(s)});
    }
    return LsBounds{s, ones};
  }
  // s <u x: [s + 1, ones], empty for s = ones; s >=u x: [0, s].
  if (holds)
  {
    return isOnes(s) ? std::nullopt
                     : std::optional<LsBounds>(LsBounds{inc(s), ones});
  }
  return LsBounds{zero, s};
}

std::optional<LsBounds> meetBounds(LsKind k,
                                   const LsBounds& a,
                                   const LsBounds& b)
{
  Assert(isIneqKind(k));
  Assert(a.lo.getSize() == b.lo.getSize());
  if (k == LsKind::SLT)
  {
    std::optional<LsBounds> m = meetBounds(LsKind::ULT,
                                           {flipMsb(a.lo), flipMsb(a.hi)},
                                           {flipMsb(b.lo), flipMsb(b.hi)});
    if (m)
    {
      return LsBounds{flipMsb(m->lo), flipMsb(m->hi)};
    }
    return m;
  }
  const LsValue& lo = a.lo.unsignedLessThan(b.lo) ? b.lo : a.lo;
  const LsValue& hi = a.hi.unsignedLessThan(b.hi) ? a.hi : b.hi;
  if (hi.unsignedLessThan(lo))
  {
    return std::nullopt;
  }
  return LsBounds{lo, hi};
}

bool isFullBounds(LsKind k, const LsBounds& b)
{
  Assert(isIneqKind(k));
  if (k == LsKind::SLT)
  {
    return isZero(flipMsb(b.lo)) && isOnes(flipMsb(b.hi));
  }
  return isZero(b.lo) && isOnes(b.hi);
}

bool usesBounds(LsKind k) { return isIneqKind(k); }

LsKind boundsKind(LsKind k)
{
  Assert(usesBounds(k));
  return k;
}

namespace {

/**
 * A sampler of inverse values, and whether the values it draws are to be
 * flipped back (SLT).
 */
struct InverseSampler
{
  DomainSampler sampler;
  bool flip;
};

/**
 * Return a sampler of the inverse values of child posX that match x and lie
 * within b, or nothing if there is none.
 */
std::optional<InverseSampler> inverseSamplerWithin(const OpInfo& op,
                                                   uint32_t posX,
                                                   const LsValue& t,
                                                   const LsChildren& ch,
                                                   const TernaryDomain& x,
                                                   const LsBounds& b)
{
  Assert(usesBounds(op.kind));
  Assert(b.lo.getSize() == x.getSize());
  switch (op.kind)
  {
    case LsKind::SLT:
    {
      FlippedChildren f(ch);
      std::optional<InverseSampler> res =
          inverseSamplerWithin(kUltOp,
                               posX,
                               t,
                               f.get(),
                               flipMsbD(x),
                               {flipMsb(b.lo), flipMsb(b.hi)});
      if (res)
      {
        res->flip = true;
      }
      return res;
    }
    case LsKind::ULT:
    {
      // The inverse values of an inequality are its solutions for t, an
      // interval; FMCAD'20 Sec. V-A draws them within the bounds.
      std::optional<LsBounds> r =
          ineqSolutions(op.kind, posX, t.isBitSet(0), *ch[1 - posX]);
      if (!r)
      {
        return std::nullopt;
      }
      std::optional<LsBounds> m = meetBounds(op.kind, *r, b);
      if (!m)
      {
        return std::nullopt;
      }
      DomainSampler sampler(x, m->lo, m->hi);
      if (sampler.empty())
      {
        return std::nullopt;
      }
      return InverseSampler{sampler, false};
    }
    default: break;
  }
  Unreachable() << "no rules within bounds for " << op.kind;
}

}  // namespace

bool isInvertibleWithin(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const LsChildren& ch,
                        const TernaryDomain& x,
                        const LsBounds& b)
{
  return inverseSamplerWithin(op, posX, t, ch, x, b).has_value();
}

LsValue inverseValueWithin(const OpInfo& op,
                           uint32_t posX,
                           const LsValue& t,
                           const LsChildren& ch,
                           const TernaryDomain& x,
                           const LsBounds& b,
                           LsRng& rng)
{
  std::optional<InverseSampler> sampler =
      inverseSamplerWithin(op, posX, t, ch, x, b);
  Assert(sampler);
  LsValue v = sampler->sampler.random(rng);
  if (sampler->flip)
  {
    v = flipMsb(v);
  }
#ifdef CVC5_ASSERTIONS
  Assert(x.matches(v));
  LsChildren chx = ch;
  chx[posX] = &v;
  Assert(evaluate(op, chx) == t)
      << "inverse value " << v << " within bounds for " << op.kind << " at "
      << posX << " does not produce " << t;
#endif
  return v;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
