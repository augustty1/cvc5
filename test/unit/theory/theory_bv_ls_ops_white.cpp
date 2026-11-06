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

}  // namespace test
}  // namespace cvc5::internal
