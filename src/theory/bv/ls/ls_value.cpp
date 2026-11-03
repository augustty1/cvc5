/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Values and randomness for propagation-based local search over bit-vectors.
 */

#include "theory/bv/ls/ls_value.h"

#include <ostream>
#include <vector>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

namespace {

/** Return the number of trailing zeros of v. Requires v != 0. */
uint32_t ctz64(uint64_t v)
{
#if defined(__GNUC__) || defined(__clang__)
  return __builtin_ctzll(v);
#else
  uint32_t n = 0;
  for (; (v & 1) == 0; v >>= 1)
  {
    ++n;
  }
  return n;
#endif
}

/** Return the position of the highest set bit of v plus 1, and 0 for 0. */
uint32_t bitLength64(uint64_t v)
{
#if defined(__GNUC__) || defined(__clang__)
  return v == 0 ? 0 : 64 - __builtin_clzll(v);
#else
  uint32_t n = 0;
  for (; v != 0; v >>= 1)
  {
    ++n;
  }
  return n;
#endif
}

}  // namespace

LsValue::LsValue(uint32_t size, const Integer& v) : d_size(size)
{
  if (isWide())
  {
    d_wide = new BitVector(size, v);
  }
  else
  {
    d_val = v.modByPow2(size).getUnsigned64();
  }
}

LsValue::LsValue(const BitVector& bv) : d_size(bv.getSize())
{
  if (isWide())
  {
    d_wide = new BitVector(bv);
  }
  else
  {
    d_val = bv.getValue().getUnsigned64();
  }
}

LsValue::LsValue(BitVector&& bv) : d_size(bv.getSize())
{
  if (isWide())
  {
    d_wide = new BitVector(std::move(bv));
  }
  else
  {
    d_val = bv.getValue().getUnsigned64();
  }
}

void LsValue::assignWide(const LsValue& o)
{
  if (this == &o)
  {
    return;
  }
  if (isWide() && o.isWide())
  {
    *d_wide = *o.d_wide;
    d_size = o.d_size;
    return;
  }
  if (isWide())
  {
    delete d_wide;
    d_val = o.d_val;
  }
  else
  {
    d_wide = new BitVector(*o.d_wide);
  }
  d_size = o.d_size;
}

LsValue LsValue::mkOnes(uint32_t size)
{
  return size > s_nativeSize ? LsValue(BitVector::mkOnes(size))
                             : raw(size, mask(size));
}

LsValue LsValue::mkMinSigned(uint32_t size)
{
  Assert(size > 0);
  return size > s_nativeSize ? LsValue(BitVector::mkMinSigned(size))
                             : raw(size, uint64_t(1) << (size - 1));
}

LsValue LsValue::mkMaxSigned(uint32_t size)
{
  Assert(size > 0);
  return size > s_nativeSize ? LsValue(BitVector::mkMaxSigned(size))
                             : raw(size, mask(size) >> 1);
}

Integer LsValue::toInteger() const
{
  return isWide() ? d_wide->getValue() : Integer(d_val);
}

BitVector LsValue::toBitVector() const
{
  return isWide() ? *d_wide : BitVector(d_size, d_val);
}

std::string LsValue::toString(uint32_t base) const
{
  return toBitVector().toString(base);
}

LsValue LsValue::leftShift(uint32_t k) const
{
  if (k >= d_size)
  {
    return mkZero(d_size);
  }
  return isWide() ? LsValue(d_wide->leftShift(BitVector(d_size, k)))
                  : raw(d_size, (d_val << k) & mask(d_size));
}

LsValue LsValue::logicalRightShift(uint32_t k) const
{
  if (k >= d_size)
  {
    return mkZero(d_size);
  }
  return isWide() ? LsValue(d_wide->logicalRightShift(BitVector(d_size, k)))
                  : raw(d_size, d_val >> k);
}

LsValue LsValue::leftShift(const LsValue& y) const
{
  Assert(d_size == y.d_size);
  return isWide() ? LsValue(d_wide->leftShift(*y.d_wide))
                  : leftShift(shiftAmount(y, d_size));
}

LsValue LsValue::logicalRightShift(const LsValue& y) const
{
  Assert(d_size == y.d_size);
  return isWide() ? LsValue(d_wide->logicalRightShift(*y.d_wide))
                  : logicalRightShift(shiftAmount(y, d_size));
}

LsValue LsValue::extract(uint32_t high, uint32_t low) const
{
  Assert(low <= high && high < d_size);
  if (isWide())
  {
    return LsValue(d_wide->extract(high, low));
  }
  uint32_t size = high - low + 1;
  return raw(size, (d_val >> low) & mask(size));
}

LsValue LsValue::concat(const LsValue& y) const
{
  if (d_size == 0)
  {
    return y;
  }
  if (d_size + y.d_size <= s_nativeSize)
  {
    // The width of y is less than 64 here, so the shift is defined.
    return raw(d_size + y.d_size, (d_val << y.d_size) | y.d_val);
  }
  return LsValue(toBitVector().concat(y.toBitVector()));
}

std::ostream& operator<<(std::ostream& os, const LsValue& x)
{
  return os << x.toString();
}

bool isZero(const LsValue& x)
{
  return x.isWide() ? x.d_wide->getValue().isZero() : x.d_val == 0;
}

bool isOnes(const LsValue& x)
{
  if (x.isWide())
  {
    return (x.d_wide->getValue() + 1).isPow2() == x.d_size + 1;
  }
  return x.d_val == LsValue::mask(x.d_size);
}

bool msb(const LsValue& x)
{
  Assert(x.getSize() > 0);
  return x.isBitSet(x.getSize() - 1);
}

uint32_t ctz(const LsValue& x)
{
  if (isZero(x))
  {
    return x.d_size;
  }
  if (x.isWide())
  {
    // v & -v keeps only the lowest set bit of v, i.e., it is 2^ctz(v).
    const Integer& v = x.d_wide->getValue();
    return v.bitwiseAnd(-v).isPow2() - 1;
  }
  return ctz64(x.d_val);
}

uint32_t clz(const LsValue& x)
{
  if (isZero(x))
  {
    return x.d_size;
  }
  // For v != 0, the length is the position of the highest set bit plus 1.
  return x.d_size
         - (x.isWide() ? x.d_wide->getValue().length() : bitLength64(x.d_val));
}

LsValue inc(const LsValue& x)
{
  if (x.isWide())
  {
    return LsValue(BitVector(x.d_size, x.d_wide->getValue() + 1));
  }
  return LsValue::raw(x.d_size, (x.d_val + 1) & LsValue::mask(x.d_size));
}

LsValue dec(const LsValue& x)
{
  if (x.isWide())
  {
    return LsValue(BitVector(x.d_size, x.d_wide->getValue() - 1));
  }
  return LsValue::raw(x.d_size, (x.d_val - 1) & LsValue::mask(x.d_size));
}

bool uaddOverflow(const LsValue& a, const LsValue& b)
{
  Assert(a.getSize() == b.getSize());
  Assert(a.getSize() > 0);
  if (a.isWide())
  {
    // Compute the exact sum on Integer. It is >= 2^w iff it needs more than
    // w bits (length() is 1 for 0, which never exceeds w >= 1).
    return (a.d_wide->getValue() + b.d_wide->getValue()).length() > a.d_size;
  }
  // The sum either wraps around 2^64 or has a bit above the width.
  uint64_t sum = a.d_val + b.d_val;
  return sum < a.d_val || (sum & ~LsValue::mask(a.d_size)) != 0;
}

bool umulOverflow(const LsValue& a, const LsValue& b)
{
  Assert(a.getSize() == b.getSize());
  Assert(a.getSize() > 0);
  if (a.isWide())
  {
    return (a.d_wide->getValue() * b.d_wide->getValue()).length() > a.d_size;
  }
  // a * b > ones iff b > floor(ones / a).
  return a.d_val != 0 && b.d_val > LsValue::mask(a.d_size) / a.d_val;
}

LsValue modInverse(const LsValue& a)
{
  Assert(a.getSize() > 0);
  Assert(a.isBitSet(0)) << "modInverse requires an odd value";
  uint32_t w = a.d_size;
  if (a.isWide())
  {
    return LsValue(w, a.d_wide->getValue().modInverse(Integer(2).pow(w)));
  }
  // Newton's iteration: if a * y = 1 (mod 2^k), then y' = y * (2 - a * y)
  // gives a * y' = 1 (mod 2^(2k)). An odd a is its own inverse modulo 8, so
  // five steps reach 3 * 2^5 = 96 >= 64 bits.
  uint64_t y = a.d_val;
  for (uint32_t i = 0; i < 5; ++i)
  {
    y *= 2 - a.d_val * y;
  }
  return LsValue::raw(w, y & LsValue::mask(w));
}

LsValue setSlice(const LsValue& x, uint32_t hi, uint32_t lo, const LsValue& v)
{
  Assert(lo <= hi);
  Assert(hi < x.getSize());
  Assert(v.getSize() == hi - lo + 1);
  if (x.isWide())
  {
    // Subtract the old bits [hi:lo] of x and add the new ones from v.
    const Integer& xv = x.d_wide->getValue();
    Integer oldSlice = xv.extractBitRange(hi - lo + 1, lo).multiplyByPow2(lo);
    Integer newSlice = v.toInteger().multiplyByPow2(lo);
    return LsValue(x.d_size, xv - oldSlice + newSlice);
  }
  uint64_t m = LsValue::mask(hi - lo + 1) << lo;
  return LsValue::raw(x.d_size, (x.d_val & ~m) | (v.d_val << lo));
}

uint32_t shiftAmount(const LsValue& s, uint32_t w)
{
  if (s.isWide())
  {
    const Integer& v = s.d_wide->getValue();
    return v >= Integer(w) ? w : v.getUnsignedInt();
  }
  return s.d_val >= w ? w : static_cast<uint32_t>(s.d_val);
}

LsValue randomDivisorAbove(const LsValue& n,
                           const LsValue& t,
                           LsRng& rng,
                           uint32_t maxTrials)
{
  Assert(n.getSize() == t.getSize());
  Assert(t.unsignedLessThan(n));
  uint32_t w = n.d_size;
  // Each trial divisor d of n gives the two divisors d and n / d.
  if (n.isWide())
  {
    const Integer& nv = n.d_wide->getValue();
    const Integer& tv = t.d_wide->getValue();
    std::vector<Integer> divisors;
    for (uint32_t i = 1; i <= maxTrials; ++i)
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
  uint64_t nv = n.d_val;
  uint64_t tv = t.d_val;
  std::vector<uint64_t> divisors;
  // d <= nv / d is d * d <= nv without overflow.
  for (uint64_t d = 1; d <= maxTrials && d <= nv / d; ++d)
  {
    if (nv % d == 0)
    {
      uint64_t q = nv / d;
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
  return LsValue::raw(w, divisors[rng.pickIndex(divisors.size())]);
}

LsRng::LsRng(uint64_t seed) : d_rng(seed) {}

bool LsRng::pickWithProb(uint32_t perMille)
{
  Assert(perMille <= 1000);
  return pickIndex(1000) < perMille;
}

bool LsRng::flipCoin() { return pickWithProb(500); }

uint32_t LsRng::pickIndex(uint32_t n)
{
  Assert(n > 0);
  uint64_t n64 = n;
  uint64_t threshold = (0 - n64) % n64;
  uint64_t r;
  do
  {
    r = d_rng();
  } while (r < threshold);
  return static_cast<uint32_t>(r % n64);
}

uint64_t LsRng::randomWord(uint32_t nbits)
{
  Assert(0 < nbits && nbits <= 64);
  // The bits come from the top of one draw.
  return d_rng() >> (64 - nbits);
}

Integer LsRng::randomBits(uint32_t nbits)
{
  Integer res(0);
  // Full 64-bit words first, then the remaining (fewer than 64) bits.
  uint32_t i = 0;
  for (; i + 64 <= nbits; i += 64)
  {
    res = res.multiplyByPow2(64) + Integer(d_rng());
  }
  uint32_t rest = nbits - i;
  if (rest > 0)
  {
    res = res.multiplyByPow2(rest) + Integer(randomWord(rest));
  }
  return res;
}

LsValue LsRng::randomValue(uint32_t w)
{
  Assert(w > 0);
  return w > LsValue::s_nativeSize ? LsValue(w, randomBits(w))
                                   : LsValue::raw(w, randomWord(w));
}

LsValue LsRng::randomInRange(const LsValue& lo, const LsValue& hi)
{
  Assert(lo.getSize() == hi.getSize());
  Assert(lo.unsignedLessThanEq(hi));
  uint32_t w = lo.getSize();
  // Rejection sampling on the bits of the size of the range. More than half
  // of the candidates are in the range, so this takes fewer than two draws on
  // average.
  if (!lo.isWide())
  {
    uint64_t range = hi.d_val - lo.d_val;
    if (range == 0)
    {
      return lo;
    }
    uint32_t nbits = bitLength64(range);
    uint64_t r;
    do
    {
      r = randomWord(nbits);
    } while (r > range);
    return LsValue::raw(w, lo.d_val + r);
  }
  Integer range = hi.d_wide->getValue() - lo.d_wide->getValue();
  if (range.isZero())
  {
    return lo;
  }
  uint32_t nbits = range.length();
  Integer r;
  do
  {
    r = randomBits(nbits);
  } while (r > range);
  return LsValue(w, lo.d_wide->getValue() + r);
}

LsValue LsRng::randomNotEqual(const LsValue& s)
{
  uint32_t w = s.getSize();
  Assert(w > 0);
  LsValue r = randomInRange(LsValue::mkZero(w), dec(LsValue::mkOnes(w)));
  if (!r.unsignedLessThan(s))
  {
    r = inc(r);
  }
  return r;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
