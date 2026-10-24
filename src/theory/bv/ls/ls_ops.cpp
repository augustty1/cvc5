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

bool isInvertible(CVC5_UNUSED const OpInfo& op,
                  CVC5_UNUSED uint32_t posX,
                  CVC5_UNUSED const LsValue& t,
                  CVC5_UNUSED const std::vector<const LsValue*>& ch)
{
  Unimplemented();
}

LsValue inverseValue(CVC5_UNUSED const OpInfo& op,
                     CVC5_UNUSED uint32_t posX,
                     CVC5_UNUSED const LsValue& t,
                     CVC5_UNUSED const std::vector<const LsValue*>& ch,
                     CVC5_UNUSED LsRng& rng)
{
  Unimplemented();
}

LsValue consistentValue(CVC5_UNUSED const OpInfo& op,
                        CVC5_UNUSED uint32_t posX,
                        CVC5_UNUSED const LsValue& t,
                        CVC5_UNUSED const std::vector<const LsValue*>& ch,
                        CVC5_UNUSED LsRng& rng)
{
  Unimplemented();
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
