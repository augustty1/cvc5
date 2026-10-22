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

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

bool isZero(const LsValue& x) 
{ 
    return x.getValue().isZero(); 
}

bool isOnes(const LsValue& x)
{
  return (x.getValue() + 1).isPow2() == x.getSize() + 1;
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
    return x.getSize();
  }
  // v & -v keeps only the lowest set bit of v, i.e., it is 2^ctz(v).
  const Integer& v = x.getValue();
  return v.bitwiseAnd(-v).isPow2() - 1;
}

uint32_t clz(const LsValue& x)
{
  if (isZero(x))
  {
    return x.getSize();
  }
  // For v != 0, length() is the position of the highest set bit plus 1.
  return x.getSize() - x.getValue().length();
}

LsValue inc(const LsValue& x) { return LsValue(x.getSize(), x.getValue() + 1); }

LsValue dec(const LsValue& x) { return LsValue(x.getSize(), x.getValue() - 1); }

bool uaddOverflow(const LsValue& a, const LsValue& b)
{
  Assert(a.getSize() == b.getSize());
  Assert(a.getSize() > 0);
  // Compute the exact sum on Integer. It is >= 2^w iff it needs more than w
  // bits (length() is 1 for 0, which never exceeds w >= 1).
  return (a.getValue() + b.getValue()).length() > a.getSize();
}

bool umulOverflow(const LsValue& a, const LsValue& b)
{
  Assert(a.getSize() == b.getSize());
  Assert(a.getSize() > 0);
  return (a.getValue() * b.getValue()).length() > a.getSize();
}

LsValue modInverse(const LsValue& a)
{
  Assert(a.getSize() > 0);
  Assert(a.isBitSet(0)) << "modInverse requires an odd value";
  uint32_t w = a.getSize();
  return LsValue(w, a.getValue().modInverse(Integer(2).pow(w)));
}

LsValue setSlice(const LsValue& x, uint32_t hi, uint32_t lo, const LsValue& v)
{
  Assert(lo <= hi);
  Assert(hi < x.getSize());
  Assert(v.getSize() == hi - lo + 1);
  // Subtract the old bits [hi:lo] of x and add the new ones from v.
  const Integer& xv = x.getValue();
  Integer oldSlice = xv.extractBitRange(hi - lo + 1, lo).multiplyByPow2(lo);
  Integer newSlice = v.getValue().multiplyByPow2(lo);
  return LsValue(x.getSize(), xv - oldSlice + newSlice);
}

uint32_t shiftAmount(const LsValue& s, uint32_t w)
{
  if (s.getValue() >= Integer(w))
  {
    return w;
  }
  return s.getValue().getUnsignedInt();
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

Integer LsRng::randomBits(uint32_t nbits)
{
  Integer res(0);
  // Full 64-bit words first.
  uint32_t i = 0;
  for (; i + 64 <= nbits; i += 64)
  {
    res = res.multiplyByPow2(64) + Integer(d_rng());
  }
  // The remaining (fewer than 64) bits come from the top of one more draw.
  uint32_t rest = nbits - i;
  if (rest > 0)
  {
    res = res.multiplyByPow2(rest) + Integer(d_rng() >> (64 - rest));
  }
  return res;
}

LsValue LsRng::randomValue(uint32_t w)
{
  Assert(w > 0);
  return LsValue(w, randomBits(w));
}

LsValue LsRng::randomInRange(const LsValue& lo, const LsValue& hi)
{
  Assert(lo.getSize() == hi.getSize());
  Assert(lo.unsignedLessThanEq(hi));
  uint32_t w = lo.getSize();
  Integer range = hi.getValue() - lo.getValue();
  if (range.isZero())
  {
    return lo;
  }
  if (isZero(lo) && isOnes(hi))
  {
    return randomValue(w);
  }
  uint32_t nbits = range.length();
  Integer r;
  do
  {
    r = randomBits(nbits);
  } while (r > range);
  return LsValue(w, lo.getValue() + r);
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
