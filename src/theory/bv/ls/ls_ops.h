/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Operator semantics for propagation-based local search over bit-vectors:
 * evaluation, invertibility conditions, inverse and consistent values.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_OPS_H
#define CVC5__THEORY__BV__LS__LS_OPS_H

#include <cstdint>
#include <iosfwd>
#include <vector>

#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

/**
 * The kinds of local search nodes: two leaf kinds and the base operators.
 *
 * Booleans are values of width 1 (true = 1), so Boolean not, and, = and ite
 * are NOT, AND, EQ and ITE at width 1. Division and remainder are total, as
 * in SMT-LIB: x / 0 = ones and x mod 0 = x. Shifts follow SMT-LIB: both
 * operands have the same width and shifting by w or more bits gives 0 (FMSD'17
 * instead restricts w to 2^q with a q-bit shift amount).
 */
enum class LsKind
{
  CONST,    // constant leaf
  VAR,      // variable leaf
  NOT,      // ~x
  AND,      // x & y
  EQ,       // x = y, width 1
  ULT,      // x <u y, width 1
  ADD,      // x + y
  MUL,      // x * y
  UDIV,     // x / y
  UREM,     // x mod y
  SHL,      // x << y
  LSHR,     // x >> y (logical)
  CONCAT,   // x o y, x is the most significant part
  EXTRACT,  // x[hi:lo]
  ITE,      // c ? x : y, c of width 1
};

const char* toString(LsKind k);
std::ostream& operator<<(std::ostream& os, LsKind k);

/** Return the number of children of an operator of kind k (0 for leaves). */
uint32_t arity(LsKind k);

/** An operator: its kind and, for EXTRACT, the indices hi >= lo. */
struct OpInfo
{
  LsKind kind;
  uint32_t hi = 0;
  uint32_t lo = 0;
};

/**
 * The functions below take the current values of the operator's children in
 * ch, in order. Widths are read off the values. For the rule functions,
 * posX is the position of the child x being solved for, ch[posX] is its
 * current value, and the other children are the fixed values s.
 */

/** Return the value of op applied to the children values ch. */
LsValue evaluate(const OpInfo& op, const std::vector<const LsValue*>& ch);

/**
 * Return true if there is a value x' for child posX such that op evaluates
 * to t with the other children fixed (the invertibility condition). Does not
 * draw random numbers.
 */
bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const std::vector<const LsValue*>& ch);

/**
 * Return a random value x' for child posX such that op evaluates to t with
 * the other children fixed. Requires isInvertible(op, posX, t, ch).
 */
LsValue inverseValue(const OpInfo& op,
                     uint32_t posX,
                     const LsValue& t,
                     const std::vector<const LsValue*>& ch,
                     LsRng& rng);

/**
 * Return a random value x' for child posX such that op evaluates to t for
 * some values of the other children. For the base operators such a value
 * always exists.
 */
LsValue consistentValue(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const std::vector<const LsValue*>& ch,
                        LsRng& rng);

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_OPS_H */
