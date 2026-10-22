/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Values and randomness for propagation-based local search over bit-vectors.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_VALUE_H
#define CVC5__THEORY__BV__LS__LS_VALUE_H

#include "util/bitvector.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

using LsValue = cvc5::internal::BitVector;

/**
 * The random number generator of the local search.
 *
 * It owns its own cvc5::internal::Random and never uses the global
 * Random::getRandom() singleton, so other components cannot perturb a run.
 * All methods are built on the raw 64-bit draws of the underlying
 * std::mt19937_64 (no std distributions), so a seed yields the same sequence
 * on every platform.
 */
class LsRng
{
 public:
  explicit LsRng(uint64_t seed);

  /** Return true with probability perMille / 1000 (perMille <= 1000). */
  bool pickWithProb(uint32_t perMille);

  /** Return true with probability 1/2. */
  bool flipCoin();

  /** Return a uniform index in [0, n). Requires n > 0. */
  uint32_t pickIndex(uint32_t n);

  /** Return a uniform value of width w. Requires w > 0. */
  LsValue randomValue(uint32_t w);

  /**
   * Return a uniform value in the unsigned range [lo, hi]. Requires lo and hi
   * to have the same width and lo <= hi.
   */
  LsValue randomInRange(const LsValue& lo, const LsValue& hi);

  /** Return a uniform value of the width of s that is different from s. */
  LsValue randomNotEqual(const LsValue& s);

 private:
  /** Return a uniform integer in [0, 2^nbits). */
  Integer randomBits(uint32_t nbits);

  Random d_rng;
};

/** Return true if all bits of x are 0. */
bool isZero(const LsValue& x);

/**
 * Return true if all bits of x are 1, i.e., x = 2^w - 1
 */
bool isOnes(const LsValue& x);

/** Return the most significant bit of x. Requires width >= 1. */
bool msb(const LsValue& x);

/** Return the number of trailing zeros of x, and the width w if x = 0. */
uint32_t ctz(const LsValue& x);

/** Return the number of leading zeros of x, and the width w if x = 0. */
uint32_t clz(const LsValue& x);

/** Return x + 1 modulo 2^w, i.e., inc(ones) = 0. */
LsValue inc(const LsValue& x);

/** Return x - 1 modulo 2^w, i.e., dec(0) = ones. */
LsValue dec(const LsValue& x);

/** Return true if a + b >= 2^w (unsigned). a and b must have the same width. */
bool uaddOverflow(const LsValue& a, const LsValue& b);

/** Return true if a * b >= 2^w (unsigned). a and b must have the same width. */
bool umulOverflow(const LsValue& a, const LsValue& b);

/**
 * Return the multiplicative inverse of a modulo 2^w, i.e., the y with
 * a * y = 1 (mod 2^w). Requires a to be odd.
 */
LsValue modInverse(const LsValue& a);

/**
 * Return x with bits [hi:lo] replaced by v. Requires lo <= hi < w and
 * width(v) = hi - lo + 1.
 */
LsValue setSlice(const LsValue& x, uint32_t hi, uint32_t lo, const LsValue& v);

/**
 * Return the shift amount s as an integer, saturated at w: w if s >= w,
 * otherwise s. Shifting a w-bit value by w or more bits gives 0.
 */
uint32_t shiftAmount(const LsValue& s, uint32_t w);

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_VALUE_H */
