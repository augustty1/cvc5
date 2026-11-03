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

#include <iosfwd>
#include <string>

#include "util/bitvector.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

class LsRng;

/**
 * A bit-vector value of the local search.
 *
 * Values of width up to 64 are stored in a machine word and computed with
 * native arithmetic, so that copying and operating on them does not allocate.
 * Wider values are kept in a heap-allocated BitVector and every operation on
 * them is delegated to it.
 *
 * The interface is the subset of the BitVector interface that the local
 * search uses, with the same semantics: operands of binary operations must
 * have the same width, arithmetic is modulo 2^w, and division and remainder
 * are total (x / 0 = ones, x mod 0 = x).
 */
class LsValue
{
 public:
  /** The largest width that is stored in a machine word. */
  static constexpr uint32_t s_nativeSize = 64;

  /** The value of width 0. */
  LsValue() : d_size(0), d_val(0) {}
  /** The value v modulo 2^size. */
  LsValue(uint32_t size, uint64_t v) : d_size(size)
  {
    if (isWide())
    {
      d_wide = new BitVector(size, v);
    }
    else
    {
      d_val = v & mask(size);
    }
  }
  /** The value v modulo 2^size. */
  LsValue(uint32_t size, const Integer& v);
  explicit LsValue(const BitVector& bv);
  explicit LsValue(BitVector&& bv);

  LsValue(const LsValue& o) : d_size(o.d_size)
  {
    if (isWide())
    {
      d_wide = new BitVector(*o.d_wide);
    }
    else
    {
      d_val = o.d_val;
    }
  }
  LsValue(LsValue&& o) noexcept : d_size(o.d_size)
  {
    // Narrow values are copied; a wide value hands over its BitVector and
    // becomes the value of width 0.
    d_val = o.d_val;
    if (isWide())
    {
      d_wide = o.d_wide;
      o.d_size = 0;
      o.d_val = 0;
    }
  }
  LsValue& operator=(const LsValue& o)
  {
    if (isWide() || o.isWide())
    {
      assignWide(o);
    }
    else
    {
      d_size = o.d_size;
      d_val = o.d_val;
    }
    return *this;
  }
  LsValue& operator=(LsValue&& o) noexcept
  {
    if (this != &o)
    {
      if (isWide())
      {
        delete d_wide;
      }
      d_size = o.d_size;
      d_val = o.d_val;
      if (isWide())
      {
        d_wide = o.d_wide;
        o.d_size = 0;
        o.d_val = 0;
      }
    }
    return *this;
  }
  ~LsValue()
  {
    if (isWide())
    {
      delete d_wide;
    }
  }

  static LsValue mkZero(uint32_t size) { return LsValue(size, uint64_t(0)); }
  static LsValue mkOne(uint32_t size) { return LsValue(size, uint64_t(1)); }
  static LsValue mkOnes(uint32_t size);
  /** The value 10...0. */
  static LsValue mkMinSigned(uint32_t size);
  /** The value 01...1. */
  static LsValue mkMaxSigned(uint32_t size);

  uint32_t getSize() const { return d_size; }
  /** Return the value as an unsigned integer. */
  Integer toInteger() const;
  BitVector toBitVector() const;
  std::string toString(uint32_t base = 2) const;

  /** Return bit i, where bit 0 is the least significant. Requires i < w. */
  bool isBitSet(uint32_t i) const
  {
    return isWide() ? d_wide->isBitSet(i) : ((d_val >> i) & 1) != 0;
  }

  bool operator==(const LsValue& y) const
  {
    if (d_size != y.d_size)
    {
      return false;
    }
    return isWide() ? *d_wide == *y.d_wide : d_val == y.d_val;
  }
  bool operator!=(const LsValue& y) const { return !(*this == y); }
  bool unsignedLessThan(const LsValue& y) const
  {
    return isWide() ? d_wide->unsignedLessThan(*y.d_wide) : d_val < y.d_val;
  }
  bool unsignedLessThanEq(const LsValue& y) const
  {
    return isWide() ? d_wide->unsignedLessThanEq(*y.d_wide) : d_val <= y.d_val;
  }

  LsValue operator~() const
  {
    return isWide() ? LsValue(~*d_wide) : raw(d_size, ~d_val & mask(d_size));
  }
  LsValue operator&(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide & *y.d_wide)
                    : raw(d_size, d_val & y.d_val);
  }
  LsValue operator|(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide | *y.d_wide)
                    : raw(d_size, d_val | y.d_val);
  }
  LsValue operator^(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide ^ *y.d_wide)
                    : raw(d_size, d_val ^ y.d_val);
  }
  LsValue operator+(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide + *y.d_wide)
                    : raw(d_size, (d_val + y.d_val) & mask(d_size));
  }
  LsValue operator-(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide - *y.d_wide)
                    : raw(d_size, (d_val - y.d_val) & mask(d_size));
  }
  LsValue operator-() const
  {
    return isWide() ? LsValue(-*d_wide)
                    : raw(d_size, (uint64_t(0) - d_val) & mask(d_size));
  }
  LsValue operator*(const LsValue& y) const
  {
    return isWide() ? LsValue(*d_wide * *y.d_wide)
                    : raw(d_size, (d_val * y.d_val) & mask(d_size));
  }
  /** Unsigned division, with x / 0 = ones. */
  LsValue unsignedDivTotal(const LsValue& y) const
  {
    if (isWide())
    {
      return LsValue(d_wide->unsignedDivTotal(*y.d_wide));
    }
    return raw(d_size, y.d_val == 0 ? mask(d_size) : d_val / y.d_val);
  }
  /** Unsigned remainder, with x mod 0 = x. */
  LsValue unsignedRemTotal(const LsValue& y) const
  {
    if (isWide())
    {
      return LsValue(d_wide->unsignedRemTotal(*y.d_wide));
    }
    return raw(d_size, y.d_val == 0 ? d_val : d_val % y.d_val);
  }

  /** Shift by k bits, filling in zeros. The result is 0 if k >= w. */
  LsValue leftShift(uint32_t k) const;
  LsValue logicalRightShift(uint32_t k) const;
  /** Shift by the value of y, which has the same width. */
  LsValue leftShift(const LsValue& y) const;
  LsValue logicalRightShift(const LsValue& y) const;

  /** Return bits [high:low]. Requires low <= high < w. */
  LsValue extract(uint32_t high, uint32_t low) const;
  /** Return this o y, where this is the most significant part. */
  LsValue concat(const LsValue& y) const;

 private:
  friend class LsRng;
  friend bool isZero(const LsValue& x);
  friend bool isOnes(const LsValue& x);
  friend uint32_t ctz(const LsValue& x);
  friend uint32_t clz(const LsValue& x);
  friend LsValue inc(const LsValue& x);
  friend LsValue dec(const LsValue& x);
  friend bool uaddOverflow(const LsValue& a, const LsValue& b);
  friend bool umulOverflow(const LsValue& a, const LsValue& b);
  friend LsValue modInverse(const LsValue& a);
  friend LsValue setSlice(const LsValue& x,
                          uint32_t hi,
                          uint32_t lo,
                          const LsValue& v);
  friend uint32_t shiftAmount(const LsValue& s, uint32_t w);
  friend LsValue randomDivisorAbove(const LsValue& n,
                                    const LsValue& t,
                                    LsRng& rng,
                                    uint32_t maxTrials);

  /** Return the value with the low w bits set. Requires w <= 64. */
  static uint64_t mask(uint32_t w)
  {
    return w >= 64 ? ~uint64_t(0) : (uint64_t(1) << w) - 1;
  }
  /** Return the value v of width size <= 64. Requires v < 2^size. */
  static LsValue raw(uint32_t size, uint64_t v)
  {
    LsValue res;
    res.d_size = size;
    res.d_val = v;
    return res;
  }

  bool isWide() const { return d_size > s_nativeSize; }
  /** Assignment when this or o is wide. */
  void assignWide(const LsValue& o);

  /** The width. */
  uint32_t d_size;
  union
  {
    /** The value if the width is at most 64; the bits above it are 0. */
    uint64_t d_val;
    /** The value otherwise, owned. */
    BitVector* d_wide;
  };
};

std::ostream& operator<<(std::ostream& os, const LsValue& x);

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
  /** Return a uniform integer in [0, 2^nbits), for 0 < nbits <= 64. */
  uint64_t randomWord(uint32_t nbits);
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

/**
 * Return a random divisor d > t of n, or n if trial division by 1, ...,
 * maxTrials finds none. Requires n > t.
 */
LsValue randomDivisorAbove(const LsValue& n,
                           const LsValue& t,
                           LsRng& rng,
                           uint32_t maxTrials);

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_VALUE_H */
