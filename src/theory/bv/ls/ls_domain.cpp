/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Ternary domains for propagation-based local search over bit-vectors.
 */

#include "theory/bv/ls/ls_domain.h"

#include <ostream>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

TernaryDomain::TernaryDomain(const LsValue& l, const LsValue& h)
    : d_lo(l), d_hi(h)
{
  Assert(isValid(d_lo, d_hi))
      << "invalid domain <" << d_lo << ", " << d_hi << ">";
}

TernaryDomain TernaryDomain::full(uint32_t w)
{
  return TernaryDomain(LsValue::mkZero(w), LsValue::mkOnes(w));
}

TernaryDomain TernaryDomain::fixed(const LsValue& v)
{
  return TernaryDomain(v, v);
}

TernaryDomain TernaryDomain::fromString(const std::string& s)
{
  uint32_t w = s.size();
  Assert(w > 0);
  LsValue one = LsValue::mkOne(1);
  LsValue lo = LsValue::mkZero(w);
  LsValue hi = LsValue::mkZero(w);
  for (uint32_t i = 0; i < w; ++i)
  {
    char c = s[w - 1 - i];
    Assert(c == '0' || c == '1' || c == 'x') << "unexpected '" << c << "'";
    if (c == '1')
    {
      lo = setSlice(lo, i, i, one);
    }
    if (c != '0')
    {
      hi = setSlice(hi, i, i, one);
    }
  }
  return TernaryDomain(lo, hi);
}

bool TernaryDomain::isValid(const LsValue& l, const LsValue& h)
{
  return l.getSize() == h.getSize() && isZero(l & ~h);
}

uint32_t TernaryDomain::numFree() const
{
  uint32_t n = 0;
  for (uint32_t i = 0, w = getSize(); i < w; ++i)
  {
    if (!isFixedBit(i))
    {
      ++n;
    }
  }
  return n;
}

std::string TernaryDomain::toString() const
{
  uint32_t w = getSize();
  std::string s(w, 'x');
  for (uint32_t i = 0; i < w; ++i)
  {
    if (isFixedBit(i))
    {
      s[w - 1 - i] = d_lo.isBitSet(i) ? '1' : '0';
    }
  }
  return s;
}

std::ostream& operator<<(std::ostream& os, const TernaryDomain& x)
{
  return os << x.toString();
}

TernaryDomain notD(const TernaryDomain& x)
{
  return TernaryDomain(~x.hi(), ~x.lo());
}

TernaryDomain andD(const TernaryDomain& x, const TernaryDomain& y)
{
  Assert(x.getSize() == y.getSize());
  // A bit is 1 iff it is 1 in both, and it can be 1 iff it can be in both.
  return TernaryDomain(x.lo() & y.lo(), x.hi() & y.hi());
}

TernaryDomain extractD(const TernaryDomain& x, uint32_t high, uint32_t low)
{
  return TernaryDomain(x.lo().extract(high, low), x.hi().extract(high, low));
}

TernaryDomain concatD(const TernaryDomain& x, const TernaryDomain& y)
{
  return TernaryDomain(x.lo().concat(y.lo()), x.hi().concat(y.hi()));
}

TernaryDomain shlD(const TernaryDomain& x, uint32_t k)
{
  // The zeros shifted in are 0 in both lo and hi, i.e., fixed to 0.
  return TernaryDomain(x.lo().leftShift(k), x.hi().leftShift(k));
}

TernaryDomain lshrD(const TernaryDomain& x, uint32_t k)
{
  return TernaryDomain(x.lo().logicalRightShift(k),
                       x.hi().logicalRightShift(k));
}

std::optional<TernaryDomain> meet(const TernaryDomain& x,
                                  const TernaryDomain& y)
{
  Assert(x.getSize() == y.getSize());
  LsValue l = x.lo() | y.lo();
  LsValue h = x.hi() & y.hi();
  if (!TernaryDomain::isValid(l, h))
  {
    // Some bit is fixed to 1 in one domain and to 0 in the other.
    return std::nullopt;
  }
  return TernaryDomain(l, h);
}

TernaryDomain join(const TernaryDomain& x, const TernaryDomain& y)
{
  Assert(x.getSize() == y.getSize());
  return TernaryDomain(x.lo() & y.lo(), x.hi() | y.hi());
}

LsValue compress(const TernaryDomain& x, const LsValue& v)
{
  uint32_t w = x.getSize();
  Assert(v.getSize() == w);
  uint32_t k = 0;
  if (w <= LsValue::s_nativeSize)
  {
    uint64_t res = 0;
    for (uint32_t i = 0; i < w; ++i)
    {
      if (!x.isFixedBit(i))
      {
        res |= uint64_t(v.isBitSet(i)) << k;
        ++k;
      }
    }
    Assert(k > 0);
    return LsValue(k, res);
  }
  Integer res(0);
  for (uint32_t i = 0; i < w; ++i)
  {
    if (!x.isFixedBit(i))
    {
      if (v.isBitSet(i))
      {
        res.setBit(k, true);
      }
      ++k;
    }
  }
  Assert(k > 0);
  return LsValue(k, res);
}

LsValue expand(const TernaryDomain& x, const LsValue& c)
{
  uint32_t w = x.getSize();
  uint32_t k = 0;
  if (w <= LsValue::s_nativeSize)
  {
    uint64_t res = 0;
    for (uint32_t i = 0; i < w; ++i)
    {
      if (!x.isFixedBit(i))
      {
        res |= uint64_t(c.isBitSet(k)) << i;
        ++k;
      }
    }
    Assert(k == c.getSize());
    // The free bits are 0 in lo, which adds the bits fixed to 1.
    return LsValue(w, res) | x.lo();
  }
  Integer res(0);
  for (uint32_t i = 0; i < w; ++i)
  {
    if (!x.isFixedBit(i))
    {
      if (c.isBitSet(k))
      {
        res.setBit(i, true);
      }
      ++k;
    }
  }
  Assert(k == c.getSize());
  return LsValue(w, res) | x.lo();
}

std::optional<LsValue> minMatchingGeq(const TernaryDomain& x, const LsValue& a)
{
  uint32_t w = x.getSize();
  Assert(a.getSize() == w);
  LsValue freeBits = x.freeMask();
  // The fixed bits where a differs from x. lo is 0 at the free bits, so it
  // holds exactly the bits fixed to 1.
  LsValue diff = (a ^ x.lo()) & ~freeBits;
  if (isZero(diff))
  {
    return a;
  }
  // The highest such bit, i, decides: the bits of a above it match x.
  uint32_t i = w - 1 - clz(diff);
  LsValue above = LsValue::mkOnes(w).leftShift(i + 1);
  if (x.lo().isBitSet(i))
  {
    // a has a 0 where x has a 1. Any matching value that agrees with a above
    // i is greater than a; the smallest one has its free bits below i at 0.
    return (a & above & freeBits) | x.lo();
  }
  // a has a 1 where x has a 0, so a matching value that agrees with a above i
  // is smaller than a: the free bits above i, read as a number, must be
  // incremented. Setting all other bits to 1 makes the carry of + 1 skip
  // them and end at the lowest free 0 above i; it also clears the free bits
  // below that one, which gives the smallest such value.
  LsValue q = a | ~(freeBits & above);
  if (isOnes(q))
  {
    return std::nullopt;  // the free bits above i are all 1 already
  }
  return (inc(q) & freeBits & above) | x.lo();
}

std::optional<LsValue> maxMatchingLeq(const TernaryDomain& x, const LsValue& b)
{
  // v <= b iff ~v >= ~b, and v matches x iff ~v matches ~x.
  std::optional<LsValue> res = minMatchingGeq(notD(x), ~b);
  if (!res)
  {
    return std::nullopt;
  }
  return ~*res;
}

bool hasMatchingIn(const TernaryDomain& x, const LsValue& a, const LsValue& b)
{
  std::optional<LsValue> first = minMatchingGeq(x, a);
  return first && first->unsignedLessThanEq(b);
}

LsValue pick(const TernaryDomain& x, LsRng& rng)
{
  // Every matching value is the image of the same number of values.
  return x.apply(rng.randomValue(x.getSize()));
}

LsValue pick(const TernaryDomain& x,
             const LsValue& a,
             const LsValue& b,
             LsRng& rng)
{
  Assert(a.unsignedLessThanEq(b));
  if (!x.hasFixedBits())
  {
    return rng.randomInRange(a, b);
  }
  std::optional<LsValue> first = minMatchingGeq(x, a);
  std::optional<LsValue> last = maxMatchingLeq(x, b);
  Assert(first && last && first->unsignedLessThanEq(*last))
      << "no value in [" << a << ", " << b << "] matches " << x;
  if (*first == *last)
  {
    return *first;
  }
  return expand(x, rng.randomInRange(compress(x, *first), compress(x, *last)));
}

LsValue pickNotEqual(const TernaryDomain& x, const LsValue& s, LsRng& rng)
{
  Assert(!x.isFixed() || x.lo() != s)
      << "the only value matching " << x << " is " << s;
  if (!x.hasFixedBits())
  {
    return rng.randomNotEqual(s);
  }
  if (!x.matches(s))
  {
    return pick(x, rng);
  }
  // s matches x, so x is not fixed and compress is defined.
  return expand(x, rng.randomNotEqual(compress(x, s)));
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
