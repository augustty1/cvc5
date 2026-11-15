/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Ternary domains for propagation-based local search over bit-vectors
 * (FMCAD'20 Sec. IV): the constant bits of a node, and values that match
 * them.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_DOMAIN_H
#define CVC5__THEORY__BV__LS__LS_DOMAIN_H

#include <iosfwd>
#include <optional>
#include <string>

#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

/**
 * A ternary bit-vector: every bit is fixed to 0, fixed to 1, or free.
 *
 * It is represented as the pair <lo, hi> of FMCAD'20: a bit fixed to 0 is 0
 * in both, a bit fixed to 1 is 1 in both, and a free bit is 0 in lo and 1 in
 * hi. The pair is valid iff no bit is 1 in lo and 0 in hi. A value matches
 * the domain if it agrees with every fixed bit; lo is the smallest and hi
 * the largest matching value (unsigned).
 */
struct TernaryDomain
{
  /** The domain of width 0. */
  TernaryDomain() {}
  /** The domain <l, h>. Requires it to be valid. */
  TernaryDomain(const LsValue& l, const LsValue& h);

  /** The domain of width w without fixed bits. */
  static TernaryDomain full(uint32_t w);
  /** The domain whose only matching value is v. */
  static TernaryDomain fixed(const LsValue& v);
  /**
   * The domain written as a string of '0', '1' and 'x' (free), most
   * significant bit first, e.g., "1x0".
   */
  static TernaryDomain fromString(const std::string& s);

  uint32_t getSize() const { return lo.getSize(); }
  /** Return true if lo and hi have the same width and no bit is 1 in lo and
   * 0 in hi. */
  bool isValid() const;
  /** Return true if every bit is fixed. */
  bool isFixed() const { return lo == hi; }
  /** Return true if some bit is fixed. */
  bool hasFixedBits() const { return !isZero(lo) || !isOnes(hi); }
  /** Return true if bit i is fixed (to 1, to 0). Requires i < w. */
  bool isFixedBit(uint32_t i) const { return lo.isBitSet(i) == hi.isBitSet(i); }
  bool isFixedTrue(uint32_t i) const { return lo.isBitSet(i); }
  bool isFixedFalse(uint32_t i) const { return !hi.isBitSet(i); }
  /** Return the value with a 1 at every free bit. */
  LsValue freeMask() const { return lo ^ hi; }
  /** Return the number of free bits. */
  uint32_t numFree() const;

  /**
   * Return true if v matches the fixed bits (FMCAD'20 Def. 1, mcb). Requires
   * v to have the width of the domain.
   */
  bool matches(const LsValue& v) const
  {
    return (hi & v) == v && (lo | v) == v;
  }
  /** Return v with the fixed bits forced in, which matches the domain. */
  LsValue apply(const LsValue& v) const { return (v & hi) | lo; }

  /** Like fromString. */
  std::string toString() const;

  bool operator==(const TernaryDomain& o) const
  {
    return lo == o.lo && hi == o.hi;
  }
  bool operator!=(const TernaryDomain& o) const { return !(*this == o); }

  /** The fixed 1s; 0 at the free bits. */
  LsValue lo;
  /** The complement of the fixed 0s; 1 at the free bits. */
  LsValue hi;
};

std::ostream& operator<<(std::ostream& os, const TernaryDomain& x);

/*
 * Domains of operators. For an operator op, the result describes the values
 * op(v, ...) for v, ... matching the arguments. All of them are exact: a bit
 * of the result is fixed iff it is the same for all such values.
 */

/** The domain of ~v. */
TernaryDomain notD(const TernaryDomain& x);
/** The domain of v & u. Requires equal widths. */
TernaryDomain andD(const TernaryDomain& x, const TernaryDomain& y);
/** The domain of v[high:low]. Requires low <= high < w. */
TernaryDomain extractD(const TernaryDomain& x, uint32_t high, uint32_t low);
/** The domain of v o u, where v is the most significant part. */
TernaryDomain concatD(const TernaryDomain& x, const TernaryDomain& y);
/** The domain of v << k for the constant k; fixed to 0 if k >= w. */
TernaryDomain shlD(const TernaryDomain& x, uint32_t k);
/** The domain of v >> k (logical) for the constant k. */
TernaryDomain lshrD(const TernaryDomain& x, uint32_t k);

/**
 * Return the domain matched by exactly the values that match both x and y,
 * or nothing if there is no such value. Requires equal widths.
 */
std::optional<TernaryDomain> meet(const TernaryDomain& x,
                                  const TernaryDomain& y);
/**
 * Return the smallest domain matched by the values that match x or y: a bit
 * is fixed iff it is fixed to the same value in both. Requires equal widths.
 */
TernaryDomain join(const TernaryDomain& x, const TernaryDomain& y);

/*
 * Values modulo constant bits. The matching values of x, in unsigned order,
 * correspond to the numbers 0, 1, ... written on the free bits of x:
 * compress maps a matching value to that number and expand maps it back.
 * Both preserve the order, so the matching values in a range [a, b] are a
 * contiguous range of numbers. This is the idea of Bitwuzla's
 * BitVectorDomainGenerator. None of the functions without an LsRng argument
 * draws random numbers.
 */

/**
 * Return the free bits of v, packed into a value of width numFree(). Requires
 * x to have a free bit and v to have the width of x.
 */
LsValue compress(const TernaryDomain& x, const LsValue& v);
/**
 * Return the matching value whose free bits are c. Requires c to have width
 * numFree() > 0.
 */
LsValue expand(const TernaryDomain& x, const LsValue& c);

/** Return the smallest v >= a that matches x, if there is one. */
std::optional<LsValue> minMatchingGeq(const TernaryDomain& x, const LsValue& a);
/** Return the largest v <= b that matches x, if there is one. */
std::optional<LsValue> maxMatchingLeq(const TernaryDomain& x, const LsValue& b);
/** Return true if some v with a <= v <= b matches x (false if b < a). */
bool hasMatchingIn(const TernaryDomain& x, const LsValue& a, const LsValue& b);

/** Return a uniform value among those that match x. */
LsValue pick(const TernaryDomain& x, LsRng& rng);
/**
 * Return a uniform value among those in [a, b] that match x. Requires
 * hasMatchingIn(x, a, b).
 */
LsValue pick(const TernaryDomain& x,
             const LsValue& a,
             const LsValue& b,
             LsRng& rng);
/**
 * Return a uniform value among those that match x and are different from s.
 * Requires such a value to exist, i.e., x is not fixed to s.
 */
LsValue pickNotEqual(const TernaryDomain& x, const LsValue& s, LsRng& rng);

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_DOMAIN_H */
