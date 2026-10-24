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
      LsValue x = rng.flipCoin() ? *ch[0] : rng.randomValue(w);
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
    case LsKind::ULT:
    case LsKind::MUL:
    case LsKind::UDIV:
    case LsKind::UREM:
    case LsKind::SHL:
    case LsKind::LSHR: Unimplemented() << "inverseValue for " << op.kind;
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
    case LsKind::MUL:
    case LsKind::UDIV:
    case LsKind::UREM:
    case LsKind::SHL:
    case LsKind::LSHR: Unimplemented() << "isInvertible for " << op.kind;
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "isInvertible called on leaf kind " << op.kind;
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
    case LsKind::ULT:
    case LsKind::MUL:
    case LsKind::UDIV:
    case LsKind::UREM:
    case LsKind::SHL:
    case LsKind::LSHR: Unimplemented() << "consistentValue for " << op.kind;
    case LsKind::CONST:
    case LsKind::VAR: break;
  }
  Unreachable() << "consistentValue called on leaf kind " << op.kind;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
