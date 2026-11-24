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
#include <vector>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

namespace {

/** Return the value with the low n <= 64 bits set. */
uint64_t lowMask(uint32_t n)
{
  return n >= 64 ? ~uint64_t(0) : (uint64_t(1) << n) - 1;
}

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

/** Return the number of bits of v that are 1. */
uint32_t popcount64(uint64_t v)
{
#if defined(__GNUC__) || defined(__clang__)
  return __builtin_popcountll(v);
#else
  uint32_t n = 0;
  for (; v != 0; v &= v - 1)
  {
    ++n;
  }
  return n;
#endif
}

/** Return the len <= 64 bits of words that start at bit k. */
uint64_t readBits(const uint64_t* words, uint32_t k, uint32_t len)
{
  uint32_t i = k / 64;
  uint32_t o = k % 64;
  uint64_t v = words[i] >> o;
  if (o + len > 64)
  {
    v |= words[i + 1] << (64 - o);
  }
  return v & lowMask(len);
}

/** Or v < 2^len, len <= 64, into words starting at bit k. */
void writeBits(uint64_t* words, uint32_t k, uint32_t len, uint64_t v)
{
  uint32_t i = k / 64;
  uint32_t o = k % 64;
  words[i] |= v << o;
  if (o + len > 64)
  {
    words[i + 1] |= v >> (64 - o);
  }
}

/**
 * Call f(pos, len) for each run of consecutive 1s of the mask m of n words,
 * by increasing position. A run that crosses a word boundary is passed as two
 * runs.
 */
template <class F>
void forEachRun(const uint64_t* m, uint32_t n, F f)
{
  for (uint32_t i = 0; i < n; ++i)
  {
    uint64_t mi = m[i];
    while (mi != 0)
    {
      uint32_t b = ctz64(mi);
      // The run starts at bit 0 of rest; it ends at the first 0 of rest.
      uint64_t rest = mi >> b;
      uint32_t len = rest == ~uint64_t(0) ? 64 : ctz64(~rest);
      f(64 * i + b, len);
      mi &= ~(lowMask(len) << b);
    }
  }
}

/**
 * Pack the bits of v at the 1s of the mask m (n words each) into out, from
 * the least significant one. out must hold numWords(popcount(m)) words, all
 * 0.
 */
void gatherBits(const uint64_t* v, const uint64_t* m, uint32_t n, uint64_t* out)
{
  uint32_t k = 0;
  forEachRun(m, n, [&](uint32_t pos, uint32_t len) {
    writeBits(out, k, len, readBits(v, pos, len));
    k += len;
  });
}

/**
 * The inverse of gatherBits: put the bits of c, from the least significant
 * one, at the 1s of the mask m of n words. out must hold n words, all 0.
 */
void scatterBits(const uint64_t* c,
                 const uint64_t* m,
                 uint32_t n,
                 uint64_t* out)
{
  uint32_t k = 0;
  forEachRun(m, n, [&](uint32_t pos, uint32_t len) {
    writeBits(out, pos, len, readBits(c, k, len));
    k += len;
  });
}

}  // namespace

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

uint32_t TernaryDomain::numFree() const { return popcount(freeMask()); }

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
  if (w <= LsValue::s_nativeSize)
  {
    uint64_t m, val, out = 0;
    toWords(x.freeMask(), &m);
    toWords(v, &val);
    Assert(m != 0);
    gatherBits(&val, &m, 1, &out);
    return LsValue(popcount64(m), out);
  }
  uint32_t n = numWords(w);
  // The mask, the value and the result, n words each.
  std::vector<uint64_t> buf(3 * n, 0);
  toWords(x.freeMask(), buf.data());
  toWords(v, buf.data() + n);
  uint32_t k = 0;
  for (uint32_t i = 0; i < n; ++i)
  {
    k += popcount64(buf[i]);
  }
  Assert(k > 0);
  gatherBits(buf.data() + n, buf.data(), n, buf.data() + 2 * n);
  return fromWords(k, buf.data() + 2 * n);
}

LsValue expand(const TernaryDomain& x, const LsValue& c)
{
  uint32_t w = x.getSize();
  Assert(c.getSize() == x.numFree());
  if (w <= LsValue::s_nativeSize)
  {
    uint64_t m, cval, out = 0;
    toWords(x.freeMask(), &m);
    toWords(c, &cval);
    scatterBits(&cval, &m, 1, &out);
    // The free bits are 0 in lo, which adds the bits fixed to 1.
    return LsValue(w, out) | x.lo();
  }
  uint32_t n = numWords(w);
  // The mask, c (numWords(c.getSize()) <= n words) and the result.
  std::vector<uint64_t> buf(3 * n, 0);
  toWords(x.freeMask(), buf.data());
  toWords(c, buf.data() + n);
  scatterBits(buf.data() + n, buf.data(), n, buf.data() + 2 * n);
  return fromWords(w, buf.data() + 2 * n) | x.lo();
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
  if (b.unsignedLessThan(a))
  {
    return false;
  }
  // lo is the smallest and hi the largest matching value, so if the range
  // covers one of them no search is needed.
  if (a.unsignedLessThanEq(x.lo()))
  {
    return x.lo().unsignedLessThanEq(b);
  }
  if (x.hi().unsignedLessThanEq(b))
  {
    return a.unsignedLessThanEq(x.hi());
  }
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
  DomainSampler sampler(x, a, b);
  Assert(!sampler.empty()) << "no value in [" << a << ", " << b << "] matches "
                           << x;
  return sampler.random(rng);
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

DomainSampler::DomainSampler(const TernaryDomain& x,
                             const LsValue& a,
                             const LsValue& b)
    : d_x(x)
{
  Assert(a.getSize() == x.getSize() && b.getSize() == x.getSize());
  if (b.unsignedLessThan(a))
  {
    return;
  }
  // lo is the smallest and hi the largest matching value: a range that covers
  // one of them needs no search for that end.
  std::optional<LsValue> first = a.unsignedLessThanEq(x.lo())
                                     ? std::optional<LsValue>(x.lo())
                                     : minMatchingGeq(x, a);
  std::optional<LsValue> last = x.hi().unsignedLessThanEq(b)
                                    ? std::optional<LsValue>(x.hi())
                                    : maxMatchingLeq(x, b);
  if (!first || !last || last->unsignedLessThan(*first))
  {
    return;
  }
  d_min = std::move(first);
  d_max = std::move(last);
  if (x.hasFixedBits() && *d_min != *d_max)
  {
    d_cmin = compress(x, *d_min);
    d_cmax = compress(x, *d_max);
  }
}

const LsValue& DomainSampler::min() const
{
  Assert(!empty());
  return *d_min;
}

const LsValue& DomainSampler::max() const
{
  Assert(!empty());
  return *d_max;
}

LsValue DomainSampler::random(LsRng& rng) const
{
  Assert(!empty());
  if (!d_x.hasFixedBits())
  {
    // [min, max] = [a, b]: the draw of the rules without constant bits.
    return rng.randomInRange(*d_min, *d_max);
  }
  if (*d_min == *d_max)
  {
    return *d_min;
  }
  return expand(d_x, rng.randomInRange(d_cmin, d_cmax));
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
