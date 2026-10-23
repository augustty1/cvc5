/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * White box testing of the local search operator semantics
 * (theory/bv/ls/ls_ops.h).
 */

#include <set>
#include <string>
#include <vector>

#include "test.h"
#include "theory/bv/ls/ls_ops.h"
#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {

using namespace theory::bv::ls;

namespace test {

class TestTheoryWhiteBvLsOps : public TestInternal
{
};

/** Placeholder: checks that the LS headers compile and link into a test. */
TEST_F(TestTheoryWhiteBvLsOps, skeleton)
{
  LsValue v(4, 5u);
  ASSERT_EQ(v.getSize(), 4u);
}

/* -------------------------------------------------------------------------- */
/* Value helpers                                                              */
/* -------------------------------------------------------------------------- */

/** Exhaustive for small widths: only 0 is zero, only 2^w - 1 is ones. */
TEST_F(TestTheoryWhiteBvLsOps, value_isZero_isOnes_exhaustive)
{
  for (uint32_t w = 1; w <= 8; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t v = 0; v <= ones; ++v)
    {
      LsValue x(w, v);
      ASSERT_EQ(isZero(x), v == 0) << "w=" << w << " v=" << v;
      ASSERT_EQ(isOnes(x), v == ones) << "w=" << w << " v=" << v;
    }
  }
}

/** Widths beyond 64 bits, where the values no longer fit in a machine word. */
TEST_F(TestTheoryWhiteBvLsOps, value_isZero_isOnes_wide)
{
  for (uint32_t w : {63u, 64u, 65u, 128u, 1000u})
  {
    LsValue zero = LsValue::mkZero(w);
    LsValue one = LsValue::mkOne(w);
    LsValue ones = LsValue::mkOnes(w);
    LsValue msbOnly = LsValue::mkMinSigned(w);    // 10...0
    LsValue maxSigned = LsValue::mkMaxSigned(w);  // 01...1

    ASSERT_TRUE(isZero(zero)) << "w=" << w;
    ASSERT_FALSE(isOnes(zero)) << "w=" << w;

    ASSERT_FALSE(isZero(ones)) << "w=" << w;
    ASSERT_TRUE(isOnes(ones)) << "w=" << w;

    for (const LsValue& x : {one, msbOnly, maxSigned})
    {
      ASSERT_FALSE(isZero(x)) << "w=" << w << " x=" << x;
      ASSERT_FALSE(isOnes(x)) << "w=" << w << " x=" << x;
    }

    // Values are taken modulo 2^w: -1 becomes ones and 2^w becomes zero.
    ASSERT_TRUE(isOnes(LsValue(w, Integer(-1))));
    ASSERT_TRUE(isZero(LsValue(w, Integer(2).pow(w))));
  }
}

/**
 * Exhaustive for small widths, against a reference that scans the bits one by
 * one.
 */
TEST_F(TestTheoryWhiteBvLsOps, value_msb_ctz_clz_inc_dec_exhaustive)
{
  for (uint32_t w = 1; w <= 8; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t v = 0; v <= ones; ++v)
    {
      LsValue x(w, v);

      uint32_t refCtz = 0;
      while (refCtz < w && !((v >> refCtz) & 1))
      {
        ++refCtz;
      }
      uint32_t refClz = 0;
      while (refClz < w && !((v >> (w - 1 - refClz)) & 1))
      {
        ++refClz;
      }

      ASSERT_EQ(msb(x), ((v >> (w - 1)) & 1) == 1) << "w=" << w << " v=" << v;
      ASSERT_EQ(ctz(x), refCtz) << "w=" << w << " v=" << v;
      ASSERT_EQ(clz(x), refClz) << "w=" << w << " v=" << v;
      ASSERT_EQ(inc(x), LsValue(w, (v + 1) & ones)) << "w=" << w << " v=" << v;
      ASSERT_EQ(dec(x), LsValue(w, (v - 1) & ones)) << "w=" << w << " v=" << v;
    }
  }
}

/** Widths beyond 64 bits, on values with known results. */
TEST_F(TestTheoryWhiteBvLsOps, value_msb_ctz_clz_inc_dec_wide)
{
  for (uint32_t w : {63u, 64u, 65u, 128u, 1000u})
  {
    LsValue zero = LsValue::mkZero(w);
    LsValue one = LsValue::mkOne(w);
    LsValue ones = LsValue::mkOnes(w);
    LsValue msbOnly = LsValue::mkMinSigned(w);    // 10...0
    LsValue maxSigned = LsValue::mkMaxSigned(w);  // 01...1

    ASSERT_FALSE(msb(zero));
    ASSERT_FALSE(msb(one));
    ASSERT_TRUE(msb(ones));
    ASSERT_TRUE(msb(msbOnly));
    ASSERT_FALSE(msb(maxSigned));

    ASSERT_EQ(ctz(zero), w);
    ASSERT_EQ(ctz(one), 0u);
    ASSERT_EQ(ctz(ones), 0u);
    ASSERT_EQ(ctz(msbOnly), w - 1);
    ASSERT_EQ(ctz(maxSigned), 0u);

    ASSERT_EQ(clz(zero), w);
    ASSERT_EQ(clz(one), w - 1);
    ASSERT_EQ(clz(ones), 0u);
    ASSERT_EQ(clz(msbOnly), 0u);
    ASSERT_EQ(clz(maxSigned), 1u);

    // A single bit k, and bit k together with the MSB.
    for (uint32_t k : {1u, 31u, 32u, 62u})
    {
      LsValue bitK(w, Integer(2).pow(k));
      ASSERT_EQ(ctz(bitK), k) << "w=" << w << " k=" << k;
      ASSERT_EQ(clz(bitK), w - 1 - k) << "w=" << w << " k=" << k;
      ASSERT_EQ(clz(bitK + one), w - 1 - k) << "w=" << w << " k=" << k;
      if (k < w - 1)  // otherwise bit k is the MSB itself
      {
        ASSERT_EQ(ctz(bitK + msbOnly), k) << "w=" << w << " k=" << k;
      }
    }

    // inc and dec wrap around modulo 2^w and keep the width.
    ASSERT_EQ(inc(zero), one);
    ASSERT_EQ(dec(one), zero);
    ASSERT_EQ(inc(ones), zero);
    ASSERT_EQ(dec(zero), ones);
    ASSERT_EQ(inc(maxSigned), msbOnly);
    ASSERT_EQ(dec(msbOnly), maxSigned);
    ASSERT_EQ(inc(ones).getSize(), w);
    ASSERT_EQ(dec(zero).getSize(), w);
  }
}

/** Exhaustive for small widths, against plain unsigned arithmetic. */
TEST_F(TestTheoryWhiteBvLsOps, value_overflow_modInverse_exhaustive)
{
  for (uint32_t w = 1; w <= 8; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t a = 0; a <= ones; ++a)
    {
      LsValue x(w, a);
      for (uint32_t b = 0; b <= ones; ++b)
      {
        LsValue y(w, b);
        ASSERT_EQ(uaddOverflow(x, y), a + b > ones)
            << "w=" << w << " a=" << a << " b=" << b;
        ASSERT_EQ(umulOverflow(x, y), a * b > ones)
            << "w=" << w << " a=" << a << " b=" << b;
      }
      if (a % 2 == 1)
      {
        LsValue inv = modInverse(x);
        ASSERT_EQ(inv.getSize(), w);
        ASSERT_EQ((a * inv.getValue().getUnsignedInt()) & ones, 1u)
            << "w=" << w << " a=" << a;
      }
    }
  }
}

/** Exhaustive for small widths, against a bit-by-bit reference. */
TEST_F(TestTheoryWhiteBvLsOps, value_setSlice_exhaustive)
{
  for (uint32_t w = 1; w <= 5; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t lo = 0; lo < w; ++lo)
    {
      for (uint32_t hi = lo; hi < w; ++hi)
      {
        uint32_t ws = hi - lo + 1;
        uint32_t mask = ((1u << ws) - 1) << lo;
        for (uint32_t a = 0; a <= ones; ++a)
        {
          for (uint32_t b = 0; b < (1u << ws); ++b)
          {
            uint32_t expected = (a & ~mask) | (b << lo);
            ASSERT_EQ(setSlice(LsValue(w, a), hi, lo, LsValue(ws, b)),
                      LsValue(w, expected))
                << "w=" << w << " hi=" << hi << " lo=" << lo << " a=" << a
                << " b=" << b;
          }
        }
      }
    }
  }
}

/** Exhaustive for small widths: the amount saturates at w. */
TEST_F(TestTheoryWhiteBvLsOps, value_shiftAmount_exhaustive)
{
  for (uint32_t w = 1; w <= 8; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t s = 0; s <= ones; ++s)
    {
      ASSERT_EQ(shiftAmount(LsValue(w, s), w), std::min(s, w))
          << "w=" << w << " s=" << s;
    }
  }
}

/** Widths beyond 64 bits, on values with known results. */
TEST_F(TestTheoryWhiteBvLsOps, value_overflow_modInverse_setSlice_shift_wide)
{
  for (uint32_t w : {63u, 64u, 65u, 128u, 1000u})
  {
    LsValue zero = LsValue::mkZero(w);
    LsValue one = LsValue::mkOne(w);
    LsValue two(w, 2u);
    LsValue ones = LsValue::mkOnes(w);
    LsValue msbOnly = LsValue::mkMinSigned(w);    // 10...0
    LsValue maxSigned = LsValue::mkMaxSigned(w);  // 01...1

    // uaddOverflow: the sum reaches 2^w exactly at ones + 1.
    ASSERT_FALSE(uaddOverflow(ones, zero));
    ASSERT_TRUE(uaddOverflow(ones, one));
    ASSERT_FALSE(uaddOverflow(maxSigned, maxSigned));  // 2^w - 2
    ASSERT_FALSE(uaddOverflow(maxSigned, msbOnly));    // 2^w - 1
    ASSERT_TRUE(uaddOverflow(msbOnly, msbOnly));       // 2^w

    // umulOverflow
    ASSERT_FALSE(umulOverflow(ones, zero));
    ASSERT_FALSE(umulOverflow(ones, one));
    ASSERT_TRUE(umulOverflow(ones, two));
    ASSERT_FALSE(umulOverflow(maxSigned, two));  // 2^w - 2
    ASSERT_TRUE(umulOverflow(msbOnly, two));     // 2^w
    ASSERT_TRUE(umulOverflow(ones, ones));

    // modInverse: a * modInverse(a) = 1 (mod 2^w).
    LsValue big(w, Integer(3).pow(w / 2 + 1) + 2);  // odd, spans many words
    for (const LsValue& a : {one, ones, maxSigned, big, inc(msbOnly)})
    {
      ASSERT_EQ(a * modInverse(a), one) << "w=" << w << " a=" << a;
    }
    ASSERT_EQ(modInverse(ones), ones);  // (-1) * (-1) = 1

    // setSlice: the slice gets v, the bits outside it keep their value.
    // [hi:lo] = [w-2:1] covers the 64-bit word boundary for w >= 65.
    uint32_t hi = w - 2, lo = 1;
    LsValue v = LsValue::mkOnes(hi - lo + 1);
    LsValue r = setSlice(zero, hi, lo, v);
    ASSERT_EQ(r.extract(hi, lo), v);
    ASSERT_FALSE(r.isBitSet(0));
    ASSERT_FALSE(r.isBitSet(w - 1));
    LsValue r2 = setSlice(ones, hi, lo, LsValue::mkZero(hi - lo + 1));
    ASSERT_TRUE(isZero(r2.extract(hi, lo)));
    ASSERT_TRUE(r2.isBitSet(0));
    ASSERT_TRUE(r2.isBitSet(w - 1));
    ASSERT_EQ(setSlice(ones, w - 1, 0, zero), zero);  // full slice
    ASSERT_EQ(setSlice(zero, 0, 0, LsValue::mkOne(1)), one);

    // shiftAmount saturates at w, also for amounts that do not fit in 32 bits.
    ASSERT_EQ(shiftAmount(zero, w), 0u);
    ASSERT_EQ(shiftAmount(LsValue(w, w - 1), w), w - 1);
    ASSERT_EQ(shiftAmount(LsValue(w, w), w), w);
    ASSERT_EQ(shiftAmount(ones, w), w);
    ASSERT_EQ(shiftAmount(msbOnly, w), w);
  }
}

/* -------------------------------------------------------------------------- */
/* Random number generator                                                    */
/* -------------------------------------------------------------------------- */

/**
 * Draw one of each kind from rng and append the results to out. Used to
 * compare whole sequences between generators.
 */
static void drawMixed(LsRng& rng, std::vector<std::string>& out)
{
  out.push_back(std::to_string(rng.pickIndex(1000)));
  out.push_back(std::to_string(rng.pickWithProb(300)));
  out.push_back(std::to_string(rng.flipCoin()));
  out.push_back(rng.randomValue(7).toString());
  out.push_back(rng.randomValue(130).toString());
  out.push_back(
      rng.randomInRange(LsValue(16, 100u), LsValue(16, 5000u)).toString());
  out.push_back(rng.randomNotEqual(LsValue(8, 42u)).toString());
}

/** The same seed gives the same sequence; different seeds do not. */
TEST_F(TestTheoryWhiteBvLsOps, rng_deterministic)
{
  for (uint64_t seed : {0ull, 1ull, 42ull, 0xdeadbeefcafebabeull})
  {
    LsRng a(seed), b(seed);
    std::vector<std::string> sa, sb;
    for (uint32_t i = 0; i < 200; ++i)
    {
      drawMixed(a, sa);
      drawMixed(b, sb);
    }
    ASSERT_EQ(sa, sb) << "seed=" << seed;
  }

  LsRng a(1), b(2);
  std::vector<std::string> sa, sb;
  for (uint32_t i = 0; i < 50; ++i)
  {
    drawMixed(a, sa);
    drawMixed(b, sb);
  }
  ASSERT_NE(sa, sb);
}

/** The generator does not touch the global Random singleton. */
TEST_F(TestTheoryWhiteBvLsOps, rng_independent_of_global)
{
  LsRng a(7), b(7);
  std::vector<std::string> sa, sb;
  for (uint32_t i = 0; i < 50; ++i)
  {
    drawMixed(a, sa);
    // Perturb the global generator between the draws of b.
    Random::getRandom()();
    Random::getRandom().pick<uint32_t>();
    drawMixed(b, sb);
  }
  ASSERT_EQ(sa, sb);
}

/** pickIndex stays in [0, n), hits every index, and is roughly uniform. */
TEST_F(TestTheoryWhiteBvLsOps, rng_pickIndex)
{
  LsRng rng(3);
  for (uint32_t i = 0; i < 100; ++i)
  {
    ASSERT_EQ(rng.pickIndex(1), 0u);
  }
  for (uint32_t n : {2u, 3u, 7u, 10u, 1000u})
  {
    const uint32_t perBucket = 1000;
    std::vector<uint32_t> count(n, 0);
    for (uint32_t i = 0; i < n * perBucket; ++i)
    {
      uint32_t r = rng.pickIndex(n);
      ASSERT_LT(r, n);
      ++count[r];
    }
    for (uint32_t k = 0; k < n; ++k)
    {
      // Loose bound: about 6 standard deviations for perBucket = 1000.
      ASSERT_GT(count[k], perBucket * 8 / 10) << "n=" << n << " k=" << k;
      ASSERT_LT(count[k], perBucket * 12 / 10) << "n=" << n << " k=" << k;
    }
  }
  // Large n, close to the 32-bit limit: still in range.
  for (uint32_t n : {0x80000001u, 0xffffffffu})
  {
    for (uint32_t i = 0; i < 1000; ++i)
    {
      ASSERT_LT(rng.pickIndex(n), n);
    }
  }
}

/** pickWithProb: 0 and 1000 are certain, other values roughly match. */
TEST_F(TestTheoryWhiteBvLsOps, rng_pickWithProb_flipCoin)
{
  LsRng rng(11);
  for (uint32_t i = 0; i < 1000; ++i)
  {
    ASSERT_FALSE(rng.pickWithProb(0));
    ASSERT_TRUE(rng.pickWithProb(1000));
  }
  const uint32_t n = 100000;
  for (uint32_t perMille : {1u, 100u, 250u, 500u, 999u})
  {
    uint32_t hits = 0;
    for (uint32_t i = 0; i < n; ++i)
    {
      hits += rng.pickWithProb(perMille);
    }
    double expected = n * perMille / 1000.0;
    // At most 5% relative error plus a small absolute slack for tiny p.
    ASSERT_NEAR(hits, expected, expected * 0.05 + 30) << "p=" << perMille;
  }
  uint32_t heads = 0;
  for (uint32_t i = 0; i < n; ++i)
  {
    heads += rng.flipCoin();
  }
  ASSERT_NEAR(heads, n / 2, n * 0.02);
}

/** randomValue for small widths: right width, every value is hit. */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomValue_exhaustive)
{
  LsRng rng(5);
  for (uint32_t w = 1; w <= 8; ++w)
  {
    uint32_t size = 1u << w;
    std::vector<uint32_t> count(size, 0);
    for (uint32_t i = 0; i < size * 200; ++i)
    {
      LsValue v = rng.randomValue(w);
      ASSERT_EQ(v.getSize(), w);
      ASSERT_TRUE(v.getValue() < Integer(size));
      ++count[v.getValue().getUnsignedInt()];
    }
    for (uint32_t k = 0; k < size; ++k)
    {
      ASSERT_GT(count[k], 100u) << "w=" << w << " k=" << k;
      ASSERT_LT(count[k], 300u) << "w=" << w << " k=" << k;
    }
  }
}

/**
 * randomValue for wide widths: the value fits in w bits and every bit
 * position, including the ones around the 64-bit word boundaries and the
 * msb, takes both values.
 */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomValue_wide)
{
  LsRng rng(9);
  for (uint32_t w : {63u, 64u, 65u, 127u, 128u, 129u, 1000u})
  {
    const uint32_t n = 400;
    std::vector<uint32_t> ones(w, 0);
    Integer bound = Integer(2).pow(w);
    for (uint32_t i = 0; i < n; ++i)
    {
      LsValue v = rng.randomValue(w);
      ASSERT_EQ(v.getSize(), w);
      ASSERT_TRUE(v.getValue() < bound);
      for (uint32_t b = 0; b < w; ++b)
      {
        ones[b] += v.isBitSet(b);
      }
    }
    for (uint32_t b = 0; b < w; ++b)
    {
      // Expected 200 with a standard deviation of 10.
      ASSERT_GT(ones[b], 140u) << "w=" << w << " bit=" << b;
      ASSERT_LT(ones[b], 260u) << "w=" << w << " bit=" << b;
    }
  }
}

/**
 * randomInRange for all ranges of widths 1 to 4: every result is in
 * [lo, hi] and every value in the range is hit.
 */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomInRange_exhaustive)
{
  LsRng rng(13);
  for (uint32_t w = 1; w <= 4; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t lo = 0; lo <= ones; ++lo)
    {
      for (uint32_t hi = lo; hi <= ones; ++hi)
      {
        LsValue vlo(w, lo), vhi(w, hi);
        std::set<uint32_t> seen;
        for (uint32_t i = 0; i < 400; ++i)
        {
          LsValue r = rng.randomInRange(vlo, vhi);
          ASSERT_EQ(r.getSize(), w);
          uint32_t v = r.getValue().getUnsignedInt();
          ASSERT_GE(v, lo) << "w=" << w << " lo=" << lo << " hi=" << hi;
          ASSERT_LE(v, hi) << "w=" << w << " lo=" << lo << " hi=" << hi;
          seen.insert(v);
        }
        ASSERT_EQ(seen.size(), hi - lo + 1)
            << "w=" << w << " lo=" << lo << " hi=" << hi;
      }
    }
  }
}

/** randomInRange is roughly uniform on a range that is not a power of 2. */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomInRange_uniform)
{
  LsRng rng(17);
  // [3, 12] has 10 values, so rejection sampling draws 4 bits and rejects.
  LsValue lo(8, 3u), hi(8, 12u);
  std::vector<uint32_t> count(10, 0);
  for (uint32_t i = 0; i < 10000; ++i)
  {
    ++count[rng.randomInRange(lo, hi).getValue().getUnsignedInt() - 3];
  }
  for (uint32_t k = 0; k < 10; ++k)
  {
    ASSERT_GT(count[k], 800u) << "k=" << k;
    ASSERT_LT(count[k], 1200u) << "k=" << k;
  }
}

/** randomInRange on wide values, including ranges across the 2^64 border. */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomInRange_wide)
{
  LsRng rng(19);
  for (uint32_t w : {65u, 128u, 1000u})
  {
    Integer two64 = Integer(2).pow(64);
    // A small range straddling 2^64: all 7 values are hit.
    LsValue lo(w, two64 - 3), hi(w, two64 + 3);
    std::set<std::string> seen;
    for (uint32_t i = 0; i < 300; ++i)
    {
      LsValue r = rng.randomInRange(lo, hi);
      ASSERT_EQ(r.getSize(), w);
      ASSERT_TRUE(lo.unsignedLessThanEq(r));
      ASSERT_TRUE(r.unsignedLessThanEq(hi));
      seen.insert(r.toString());
    }
    ASSERT_EQ(seen.size(), 7u) << "w=" << w;

    // Singleton ranges and the full range.
    LsValue ones = LsValue::mkOnes(w);
    LsValue zero = LsValue::mkZero(w);
    ASSERT_EQ(rng.randomInRange(lo, lo), lo);
    ASSERT_EQ(rng.randomInRange(ones, ones), ones);
    ASSERT_EQ(rng.randomInRange(zero, zero), zero);
    bool msbSet = false, msbClear = false;
    for (uint32_t i = 0; i < 100; ++i)
    {
      LsValue r = rng.randomInRange(zero, ones);
      ASSERT_EQ(r.getSize(), w);
      (msb(r) ? msbSet : msbClear) = true;
    }
    ASSERT_TRUE(msbSet && msbClear) << "w=" << w;

    // A wide range [1, ones - 1]: never returns the excluded endpoints.
    LsValue one = LsValue::mkOne(w);
    LsValue onesMinus1 = dec(ones);
    for (uint32_t i = 0; i < 200; ++i)
    {
      LsValue r = rng.randomInRange(one, onesMinus1);
      ASSERT_FALSE(isZero(r));
      ASSERT_FALSE(isOnes(r));
    }
  }
}

/**
 * randomNotEqual for widths 1 to 4: never returns s and hits every other
 * value.
 */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomNotEqual_exhaustive)
{
  LsRng rng(23);
  for (uint32_t w = 1; w <= 4; ++w)
  {
    uint32_t ones = (1u << w) - 1;
    for (uint32_t s = 0; s <= ones; ++s)
    {
      LsValue vs(w, s);
      std::set<uint32_t> seen;
      for (uint32_t i = 0; i < 400; ++i)
      {
        LsValue r = rng.randomNotEqual(vs);
        ASSERT_EQ(r.getSize(), w);
        ASSERT_NE(r, vs) << "w=" << w << " s=" << s;
        seen.insert(r.getValue().getUnsignedInt());
      }
      ASSERT_EQ(seen.size(), ones) << "w=" << w << " s=" << s;
    }
  }
}

/** randomNotEqual on wide values, including s = 0 and s = ones. */
TEST_F(TestTheoryWhiteBvLsOps, rng_randomNotEqual_wide)
{
  LsRng rng(29);
  for (uint32_t w : {64u, 65u, 128u, 1000u})
  {
    for (const LsValue& s : {LsValue::mkZero(w),
                             LsValue::mkOne(w),
                             LsValue::mkOnes(w),
                             LsValue::mkMinSigned(w),
                             rng.randomValue(w)})
    {
      for (uint32_t i = 0; i < 100; ++i)
      {
        LsValue r = rng.randomNotEqual(s);
        ASSERT_EQ(r.getSize(), w);
        ASSERT_NE(r, s) << "w=" << w;
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
