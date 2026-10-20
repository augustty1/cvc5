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

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

using LsValue = cvc5::internal::BitVector;

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
