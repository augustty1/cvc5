/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Operator semantics for propagation-based local search over bit-vectors:
 * evaluation, invertibility and consistency conditions, inverse and
 * consistent values, with and without constant bits.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_OPS_H
#define CVC5__THEORY__BV__LS__LS_OPS_H

#include <cstdint>
#include <initializer_list>
#include <iosfwd>
#include <optional>

#include "base/check.h"
#include "theory/bv/ls/ls_domain.h"
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
 *
 * The kinds after ITE are the operators that prop-c+ handles natively
 * (FMCAD'20 Sec. V), and SLT, the native <s of prop-cb+; without them the
 * adapter encodes them with the base operators. The rules of SLT are those
 * of ULT on the values and domains with the most significant bit flipped,
 * which maps the signed order to the unsigned one (plan D39).
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
  XOR,      // x ^ y
  SEXT,     // x sign-extended by n bits (n = OpInfo::hi)
  ASHR,     // x >> y (arithmetic)
  SLT,      // x <s y, width 1
};

/** The number of kinds. */
constexpr uint32_t kNumLsKinds = static_cast<uint32_t>(LsKind::SLT) + 1;

const char* toString(LsKind k);
std::ostream& operator<<(std::ostream& os, LsKind k);

/** Return the number of children of an operator of kind k (0 for leaves). */
uint32_t arity(LsKind k);

/**
 * An operator: its kind and, for EXTRACT, the indices hi >= lo; for SEXT, hi
 * is the number n >= 1 of bits added.
 */
struct OpInfo
{
  LsKind kind;
  uint32_t hi = 0;
  uint32_t lo = 0;
};

/** The largest number of children of an operator. */
constexpr uint32_t kMaxArity = 3;

/**
 * One pointer per child of an operator, in order. It does not own what it
 * points to, and it has a fixed capacity, so that building one for every
 * evaluated node does not allocate.
 */
template <class T>
class LsPointers
{
 public:
  LsPointers() : d_size(0) {}
  LsPointers(std::initializer_list<const T*> values) : d_size(0)
  {
    for (const T* v : values)
    {
      push_back(v);
    }
  }

  void push_back(const T* v)
  {
    Assert(d_size < kMaxArity);
    d_values[d_size++] = v;
  }
  uint32_t size() const { return d_size; }
  const T* operator[](uint32_t i) const
  {
    Assert(i < d_size);
    return d_values[i];
  }
  const T*& operator[](uint32_t i)
  {
    Assert(i < d_size);
    return d_values[i];
  }

 private:
  const T* d_values[kMaxArity];
  uint32_t d_size;
};

/** The values of the children of an operator. */
using LsChildren = LsPointers<LsValue>;
/** The domains of the children of an operator. */
using LsDomains = LsPointers<TernaryDomain>;

/**
 * The functions below take the current values of the operator's children in
 * ch, in order. Widths are read off the values. For the rule functions,
 * posX is the position of the child x being solved for, ch[posX] is its
 * current value, and the other children are the fixed values s.
 */

/** Return the value of op applied to the children values ch. */
LsValue evaluate(const OpInfo& op, const LsChildren& ch);

/**
 * Return true if there is a value x' for child posX such that op evaluates
 * to t with the other children fixed (the invertibility condition). Does not
 * draw random numbers.
 */
bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const LsChildren& ch);

/**
 * Return true if child i is essential for t (FMSD'17 Def. 13): no other child
 * can be changed alone to make op evaluate to t, i.e., isInvertible fails for
 * every other position. The disabled branch of an ITE counts as not
 * invertible. Trivially true for unary operators. Does not draw random
 * numbers.
 */
bool isEssential(const OpInfo& op,
                 uint32_t i,
                 const LsValue& t,
                 const LsChildren& ch);

/**
 * Return a random value x' for child posX such that op evaluates to t with
 * the other children fixed. Requires isInvertible(op, posX, t, ch).
 */
LsValue inverseValue(const OpInfo& op,
                     uint32_t posX,
                     const LsValue& t,
                     const LsChildren& ch,
                     LsRng& rng);

/**
 * Return a random value x' for child posX such that op evaluates to t for
 * some values of the other children. For the base operators such a value
 * always exists. For SEXT it exists iff isInvertible holds (the only
 * consistent value is the inverse value), which this requires.
 */
LsValue consistentValue(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const LsChildren& ch,
                        LsRng& rng);

/*
 * The rules modulo constant bits (FMCAD'20 Sec. IV). They take the domain x
 * of the child being solved for, and only produce values that match it. The
 * current value ch[posX] must match x. If x has no fixed bits, each of them
 * is the function above, with the same random draws.
 *
 * A propagation step towards child posX follows FMCAD'20 Fig. 2: if
 * isInvertible holds (and the inverse branch is chosen), the target becomes
 * inverseValue; otherwise it becomes tryConsistentValue, and if that returns
 * nothing the move ends in a conflict.
 */

/**
 * Return true if there is a value x' matching x for child posX such that op
 * evaluates to t with the other children fixed (the invertibility condition
 * modulo constant bits, FMCAD'20 Tables II-III). Does not draw random
 * numbers.
 *
 * For UREM the exact condition asks for a value in a set that can be too
 * large to search: after the exact tests, only a bounded number of
 * candidates is tried, so the result may be false although such a value
 * exists, but never the opposite. A false only sends the step to
 * tryConsistentValue, whose values include every inverse value.
 */
bool isInvertible(const OpInfo& op,
                  uint32_t posX,
                  const LsValue& t,
                  const LsChildren& ch,
                  const TernaryDomain& x);

/**
 * Return true if child i is essential for t modulo constant bits (FMCAD'20
 * Def. 5): no other child has a value matching its own domain that makes op
 * evaluate to t alone, i.e., isInvertible fails for every other position
 * with that child's domain. A child whose domain is fixed cannot change, so
 * it counts as not invertible, like the disabled branch of an ITE. doms are
 * the domains of the children. Does not draw random numbers.
 */
bool isEssential(const OpInfo& op,
                 uint32_t i,
                 const LsValue& t,
                 const LsChildren& ch,
                 const LsDomains& doms);

/**
 * Return a random value x' matching x for child posX such that op evaluates
 * to t with the other children fixed. Requires isInvertible(op, posX, t, ch,
 * x).
 */
LsValue inverseValue(const OpInfo& op,
                     uint32_t posX,
                     const LsValue& t,
                     const LsChildren& ch,
                     const TernaryDomain& x,
                     LsRng& rng);

/**
 * Return a random value x' matching x for child posX such that op evaluates
 * to t for some values of the other children (a consistent value modulo
 * constant bits, FMCAD'20 Tables IV-V), or nothing if there is none, which
 * makes the move end in a conflict. If x has no fixed bits this is
 * consistentValue(op, posX, t, ch, rng), with the same random draws, except
 * that for SEXT it is nothing if t is not a sign extension.
 *
 * Every consistent value matching x has a non-zero probability, except for
 * the branches of ITE, whose only value is t. The result is nothing iff no
 * consistent value matches x, except for UDIV at position 0, where it may
 * also be nothing, with a probability below 1, when such a value exists.
 *
 * The consistency condition and the value are one function because the
 * condition for UDIV at position 0 is decided by a search that ends with
 * random draws: a separate check without random numbers could say no for
 * ever on the same t and x although a value exists, and since a no is a
 * conflict, the search could never reach that value (plan Sec. 0.5, R2).
 */
std::optional<LsValue> tryConsistentValue(const OpInfo& op,
                                          uint32_t posX,
                                          const LsValue& t,
                                          const LsChildren& ch,
                                          const TernaryDomain& x,
                                          LsRng& rng);

/**
 * Return a domain that the value of op matches whenever the values of its
 * children match doms, computed at the word level (plan Sec. 5.2). It is
 * exact (a bit is fixed iff it is the same for all those values) for NOT,
 * AND, XOR, ADD, CONCAT, EXTRACT, SEXT, ITE, SHL, LSHR, ASHR, EQ and ULT, and
 * when all children are fixed. For MUL, UDIV and UREM it fixes the bits that
 * "known bits" rules and the bounds of the result determine, which may be
 * fewer.
 */
TernaryDomain forwardDomain(const OpInfo& op, const LsDomains& doms);

/*
 * Bounds from inequalities (prop-cb+, FMCAD'20 Sec. V-A): the satisfied
 * top-level inequalities on an operand give an interval that the inverse
 * values of other inequalities on it are drawn from.
 */

/**
 * An interval [lo, hi] of values of one width, with lo <= hi in the order of
 * the inequality kind it belongs to: unsigned for ULT, signed for SLT.
 */
struct LsBounds
{
  LsValue lo;
  LsValue hi;
};

/** Return true if k is an inequality kind whose operands can get bounds. */
bool isIneqKind(LsKind k);

/**
 * Return the values x of the width of s such that (x op s) = holds (posX =
 * 0) or (s op x) = holds (posX = 1), for the inequality kind k. They form an
 * interval in the order of k, or nothing if there is no such value.
 */
std::optional<LsBounds> ineqSolutions(LsKind k,
                                      uint32_t posX,
                                      bool holds,
                                      const LsValue& s);

/** Return the intersection of a and b for kind k, or nothing if empty. */
std::optional<LsBounds> meetBounds(LsKind k,
                                   const LsBounds& a,
                                   const LsBounds& b);

/** Return true if b contains every value of its width, for kind k. */
bool isFullBounds(LsKind k, const LsBounds& b);

/**
 * Return true if the inverse values of the children of an operator of kind k
 * can be drawn within bounds (prop-cb+): for the inequalities ULT and SLT,
 * as in FMCAD'20 Sec. V-A.
 */
bool usesBounds(LsKind k);

/**
 * Return the inequality kind whose bounds the rules of k use. Requires
 * usesBounds(k).
 */
LsKind boundsKind(LsKind k);

/**
 * Return true if there is a value x' matching x and within bounds b (in the
 * order of boundsKind(op.kind)) for child posX such that op evaluates to t
 * with the other children fixed. Requires usesBounds(op.kind). Does not draw
 * random numbers.
 */
bool isInvertibleWithin(const OpInfo& op,
                        uint32_t posX,
                        const LsValue& t,
                        const LsChildren& ch,
                        const TernaryDomain& x,
                        const LsBounds& b);

/**
 * Return a random value x' matching x and within bounds b for child posX
 * such that op evaluates to t with the other children fixed; every such
 * value has a non-zero probability. Requires isInvertibleWithin(op, posX, t,
 * ch, x, b).
 */
LsValue inverseValueWithin(const OpInfo& op,
                           uint32_t posX,
                           const LsValue& t,
                           const LsChildren& ch,
                           const TernaryDomain& x,
                           const LsBounds& b,
                           LsRng& rng);

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_OPS_H */
