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

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
