/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * White box testing of the ternary domains of the local search
 * (theory/bv/ls/ls_domain.h).
 */

#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "test.h"
#include "theory/bv/ls/ls_domain.h"
#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {

using namespace theory::bv::ls;

namespace test {

class TestTheoryWhiteBvLsDomain : public TestInternal
{
 protected:
  /** The largest width of the exhaustive tests. */
  static constexpr uint32_t kMaxWidth = 4;

  static uint32_t toUint(const LsValue& v)
  {
    return v.toInteger().getUnsignedInt();
  }

  /** All valid domains of width w: 3^w of them. */
  static std::vector<TernaryDomain> allDomains(uint32_t w)
  {
    std::vector<TernaryDomain> res;
    for (uint32_t lo = 0; lo < (1u << w); ++lo)
    {
      for (uint32_t hi = 0; hi < (1u << w); ++hi)
      {
        if ((lo & ~hi) == 0)
        {
          res.emplace_back(LsValue(w, lo), LsValue(w, hi));
        }
      }
    }
    return res;
  }

  /**
   * The values that match x, in increasing order, by the definition: v
   * matches iff it agrees with x at every fixed bit.
   */
  static std::vector<uint32_t> matching(const TernaryDomain& x)
  {
    uint32_t w = x.getSize();
    std::vector<uint32_t> res;
    for (uint32_t v = 0; v < (1u << w); ++v)
    {
      bool ok = true;
      for (uint32_t i = 0; i < w; ++i)
      {
        bool bit = ((v >> i) & 1) != 0;
        if ((x.isFixedTrue(i) && !bit) || (x.isFixedFalse(i) && bit))
        {
          ok = false;
        }
      }
      if (ok)
      {
        res.push_back(v);
      }
    }
    return res;
  }

  /**
   * Check that d is the smallest domain matched by all of values: a bit of d
   * is fixed iff all values agree on it. If exact holds, also check that the
   * values are all the values matching d.
   */
  static void checkDomainOf(const TernaryDomain& d,
                            const std::set<uint32_t>& values,
                            bool exact,
                            const std::string& ctx)
  {
    ASSERT_TRUE(TernaryDomain::isValid(d.lo(), d.hi())) << ctx;
    ASSERT_FALSE(values.empty()) << ctx;
    uint32_t w = d.getSize();
    for (uint32_t i = 0; i < w; ++i)
    {
      bool all0 = true;
      bool all1 = true;
      for (uint32_t v : values)
      {
        (((v >> i) & 1) != 0 ? all0 : all1) = false;
      }
      ASSERT_EQ(d.isFixedTrue(i), all1) << ctx << " bit " << i;
      ASSERT_EQ(d.isFixedFalse(i), all0) << ctx << " bit " << i;
    }
    if (exact)
    {
      std::vector<uint32_t> m = matching(d);
      ASSERT_EQ(std::set<uint32_t>(m.begin(), m.end()), values) << ctx;
    }
  }

  /**
   * Check that every one of the expected values was drawn, and that each was
   * drawn about kDraws times.
   */
  static void checkUniform(const std::map<uint32_t, uint32_t>& counts,
                           const std::vector<uint32_t>& expected,
                           const std::string& ctx)
  {
    ASSERT_EQ(counts.size(), expected.size()) << ctx;
    for (uint32_t v : expected)
    {
      auto it = counts.find(v);
      ASSERT_TRUE(it != counts.end()) << ctx << " never drew " << v;
      // The count is binomial with mean kDraws and deviation below 15.
      ASSERT_GE(it->second, kDraws - 90) << ctx << " value " << v;
      ASSERT_LE(it->second, kDraws + 90) << ctx << " value " << v;
    }
  }

  /** Draws per expected value in the uniformity checks. */
  static constexpr uint32_t kDraws = 200;

  LsRng d_rng{42};
};

/* -------------------------------------------------------------------------- */
/* Representation                                                             */
/* -------------------------------------------------------------------------- */

/** The examples of FMCAD'20 Sec. IV. */
TEST_F(TestTheoryWhiteBvLsDomain, paper_examples)
{
  // 1xxx is <1000, 1111>.
  TernaryDomain x = TernaryDomain::fromString("1xxx");
  ASSERT_EQ(x.lo(), LsValue(4, 0b1000));
  ASSERT_EQ(x.hi(), LsValue(4, 0b1111));
  ASSERT_EQ(x.toString(), "1xxx");

  // <1100, 1000> is invalid.
  ASSERT_FALSE(TernaryDomain::isValid(LsValue(4, 0b1100), LsValue(4, 0b1000)));
  // So are bounds of different widths.
  ASSERT_FALSE(TernaryDomain::isValid(LsValue(3, 0), LsValue(4, 0b1000)));
  ASSERT_TRUE(TernaryDomain::isValid(LsValue(4, 0b1000), LsValue(4, 0b1111)));

  // x = 1x: 11 and 10 match, 01 does not.
  TernaryDomain y = TernaryDomain::fromString("1x");
  ASSERT_EQ(y.lo(), LsValue(2, 0b10));
  ASSERT_EQ(y.hi(), LsValue(2, 0b11));
  ASSERT_TRUE(y.matches(LsValue(2, 0b11)));
  ASSERT_TRUE(y.matches(LsValue(2, 0b10)));
  ASSERT_FALSE(y.matches(LsValue(2, 0b01)));

  // x0 does not match 11 - 10 = 01 (the essential input example).
  ASSERT_FALSE(TernaryDomain::fromString("x0").matches(LsValue(2, 0b01)));
}

TEST_F(TestTheoryWhiteBvLsDomain, queries_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    std::vector<TernaryDomain> doms = allDomains(w);
    uint32_t expected = 1;
    for (uint32_t i = 0; i < w; ++i)
    {
      expected *= 3;
    }
    ASSERT_EQ(doms.size(), expected);
    for (const TernaryDomain& x : doms)
    {
      std::string ctx = x.toString();
      ASSERT_TRUE(TernaryDomain::isValid(x.lo(), x.hi())) << ctx;
      ASSERT_EQ(x.getSize(), w) << ctx;
      ASSERT_EQ(TernaryDomain::fromString(x.toString()), x) << ctx;

      uint32_t numFree = 0;
      for (uint32_t i = 0; i < w; ++i)
      {
        char c = ctx[w - 1 - i];
        ASSERT_EQ(x.isFixedBit(i), c != 'x') << ctx;
        ASSERT_EQ(x.isFixedTrue(i), c == '1') << ctx;
        ASSERT_EQ(x.isFixedFalse(i), c == '0') << ctx;
        ASSERT_EQ(x.freeMask().isBitSet(i), c == 'x') << ctx;
        numFree += c == 'x';
      }
      ASSERT_EQ(x.numFree(), numFree) << ctx;
      ASSERT_EQ(x.isFixed(), numFree == 0) << ctx;
      ASSERT_EQ(x.hasFixedBits(), numFree < w) << ctx;

      std::vector<uint32_t> m = matching(x);
      ASSERT_EQ(m.size(), 1u << numFree) << ctx;
      // lo is the smallest and hi the largest matching value.
      ASSERT_EQ(toUint(x.lo()), m.front()) << ctx;
      ASSERT_EQ(toUint(x.hi()), m.back()) << ctx;
      std::set<uint32_t> mset(m.begin(), m.end());
      for (uint32_t v = 0; v < (1u << w); ++v)
      {
        LsValue val(w, v);
        ASSERT_EQ(x.matches(val), mset.count(v) > 0) << ctx << " v=" << val;
        // apply keeps the free bits and forces the fixed ones.
        LsValue a = x.apply(val);
        ASSERT_TRUE(x.matches(a)) << ctx << " v=" << val;
        ASSERT_EQ(a & x.freeMask(), val & x.freeMask()) << ctx << " v=" << val;
        ASSERT_EQ(a == val, x.matches(val)) << ctx << " v=" << val;
      }
    }
    ASSERT_EQ(TernaryDomain::full(w).numFree(), w);
    ASSERT_FALSE(TernaryDomain::full(w).hasFixedBits());
    for (uint32_t v = 0; v < (1u << w); ++v)
    {
      TernaryDomain f = TernaryDomain::fixed(LsValue(w, v));
      ASSERT_TRUE(f.isFixed());
      ASSERT_EQ(matching(f), std::vector<uint32_t>{v});
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Domains of operators                                                       */
/* -------------------------------------------------------------------------- */

TEST_F(TestTheoryWhiteBvLsDomain, unary_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    uint32_t mask = (1u << w) - 1;
    for (const TernaryDomain& x : allDomains(w))
    {
      std::vector<uint32_t> m = matching(x);
      std::string ctx = x.toString();

      std::set<uint32_t> image;
      for (uint32_t v : m)
      {
        image.insert(~v & mask);
      }
      checkDomainOf(notD(x), image, true, "not " + ctx);

      // Shifts by a constant, including amounts of w and more.
      for (uint32_t k = 0; k <= w + 1; ++k)
      {
        std::set<uint32_t> left;
        std::set<uint32_t> right;
        for (uint32_t v : m)
        {
          left.insert(k >= w ? 0 : (v << k) & mask);
          right.insert(k >= w ? 0 : v >> k);
        }
        std::string sk = " by " + std::to_string(k);
        checkDomainOf(shlD(x, k), left, true, "shl " + ctx + sk);
        checkDomainOf(lshrD(x, k), right, true, "lshr " + ctx + sk);
      }

      for (uint32_t lo = 0; lo < w; ++lo)
      {
        for (uint32_t hi = lo; hi < w; ++hi)
        {
          std::set<uint32_t> slice;
          for (uint32_t v : m)
          {
            slice.insert((v >> lo) & ((1u << (hi - lo + 1)) - 1));
          }
          std::stringstream ss;
          ss << "extract " << ctx << "[" << hi << ":" << lo << "]";
          TernaryDomain e = extractD(x, hi, lo);
          ASSERT_EQ(e.getSize(), hi - lo + 1) << ss.str();
          checkDomainOf(e, slice, true, ss.str());
        }
      }
    }
  }
}

TEST_F(TestTheoryWhiteBvLsDomain, binary_exhaustive)
{
  for (uint32_t w = 1; w <= 3; ++w)
  {
    std::vector<TernaryDomain> doms = allDomains(w);
    for (const TernaryDomain& x : doms)
    {
      std::vector<uint32_t> mx = matching(x);
      for (const TernaryDomain& y : doms)
      {
        std::vector<uint32_t> my = matching(y);
        std::string ctx = x.toString() + " " + y.toString();

        std::set<uint32_t> conj;
        std::set<uint32_t> cat;
        std::set<uint32_t> both;
        std::set<uint32_t> either(mx.begin(), mx.end());
        either.insert(my.begin(), my.end());
        for (uint32_t v : mx)
        {
          for (uint32_t u : my)
          {
            conj.insert(v & u);
            cat.insert((v << w) | u);
            if (v == u)
            {
              both.insert(v);
            }
          }
        }
        // The values of v & u need not be all the values matching andD: for
        // 1x & x1 they are, but the bits of the result are independent.
        checkDomainOf(andD(x, y), conj, false, "and " + ctx);
        TernaryDomain c = concatD(x, y);
        ASSERT_EQ(c.getSize(), 2 * w) << ctx;
        checkDomainOf(c, cat, true, "concat " + ctx);
        checkDomainOf(join(x, y), either, false, "join " + ctx);

        std::optional<TernaryDomain> mt = meet(x, y);
        ASSERT_EQ(mt.has_value(), !both.empty()) << "meet " << ctx;
        if (mt)
        {
          checkDomainOf(*mt, both, true, "meet " + ctx);
        }
      }
    }
  }
  // Concatenation of different widths.
  TernaryDomain c = concatD(TernaryDomain::fromString("1x"),
                            TernaryDomain::fromString("x01"));
  ASSERT_EQ(c.toString(), "1xx01");
}

/* -------------------------------------------------------------------------- */
/* Values modulo constant bits                                                */
/* -------------------------------------------------------------------------- */

/** compress and expand are inverse and preserve the order. */
TEST_F(TestTheoryWhiteBvLsDomain, compress_expand_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    for (const TernaryDomain& x : allDomains(w))
    {
      if (x.isFixed())
      {
        continue;
      }
      std::vector<uint32_t> m = matching(x);
      uint32_t k = x.numFree();
      for (uint32_t i = 0; i < m.size(); ++i)
      {
        LsValue v(w, m[i]);
        LsValue c = compress(x, v);
        ASSERT_EQ(c, LsValue(k, i)) << x << " v=" << v;
        ASSERT_EQ(expand(x, c), v) << x << " c=" << c;
      }
    }
  }
}

TEST_F(TestTheoryWhiteBvLsDomain, min_max_matching_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    for (const TernaryDomain& x : allDomains(w))
    {
      std::vector<uint32_t> m = matching(x);
      for (uint32_t a = 0; a < (1u << w); ++a)
      {
        std::optional<uint32_t> geq;
        std::optional<uint32_t> leq;
        for (uint32_t v : m)
        {
          if (v >= a && !geq)
          {
            geq = v;
          }
          if (v <= a)
          {
            leq = v;
          }
        }
        LsValue av(w, a);
        std::optional<LsValue> gotGeq = minMatchingGeq(x, av);
        ASSERT_EQ(gotGeq.has_value(), geq.has_value()) << x << " a=" << av;
        if (geq)
        {
          ASSERT_EQ(toUint(*gotGeq), *geq) << x << " a=" << av;
        }
        std::optional<LsValue> gotLeq = maxMatchingLeq(x, av);
        ASSERT_EQ(gotLeq.has_value(), leq.has_value()) << x << " b=" << av;
        if (leq)
        {
          ASSERT_EQ(toUint(*gotLeq), *leq) << x << " b=" << av;
        }

        for (uint32_t b = 0; b < (1u << w); ++b)
        {
          bool expected = false;
          for (uint32_t v : m)
          {
            expected = expected || (a <= v && v <= b);
          }
          ASSERT_EQ(hasMatchingIn(x, av, LsValue(w, b)), expected)
              << x << " a=" << av << " b=" << b;
        }
      }
    }
  }
}

/** pick(x) draws every matching value, and only those, about equally often. */
TEST_F(TestTheoryWhiteBvLsDomain, pick_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    for (const TernaryDomain& x : allDomains(w))
    {
      std::vector<uint32_t> m = matching(x);
      std::map<uint32_t, uint32_t> counts;
      for (uint32_t i = 0; i < kDraws * m.size(); ++i)
      {
        LsValue v = pick(x, d_rng);
        ASSERT_EQ(v.getSize(), w);
        ASSERT_TRUE(x.matches(v)) << x << " v=" << v;
        ++counts[toUint(v)];
      }
      checkUniform(counts, m, x.toString());
    }
  }
}

/**
 * pick(x, a, b) draws only matching values of the range, for every domain
 * and range; for widths up to 3 it draws all of them about equally often.
 */
TEST_F(TestTheoryWhiteBvLsDomain, pick_range_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    for (const TernaryDomain& x : allDomains(w))
    {
      std::vector<uint32_t> m = matching(x);
      for (uint32_t a = 0; a < (1u << w); ++a)
      {
        for (uint32_t b = a; b < (1u << w); ++b)
        {
          std::vector<uint32_t> expected;
          for (uint32_t v : m)
          {
            if (a <= v && v <= b)
            {
              expected.push_back(v);
            }
          }
          if (expected.empty())
          {
            continue;
          }
          std::stringstream ctx;
          ctx << x << " [" << a << ", " << b << "]";
          LsValue av(w, a);
          LsValue bv(w, b);
          std::set<uint32_t> allowed(expected.begin(), expected.end());
          std::map<uint32_t, uint32_t> counts;
          uint32_t draws = w <= 3 ? kDraws * expected.size() : 16;
          for (uint32_t i = 0; i < draws; ++i)
          {
            LsValue v = pick(x, av, bv, d_rng);
            ASSERT_EQ(v.getSize(), w);
            ASSERT_TRUE(allowed.count(toUint(v))) << ctx.str() << " v=" << v;
            ++counts[toUint(v)];
          }
          if (w <= 3)
          {
            checkUniform(counts, expected, ctx.str());
          }
        }
      }
    }
  }
}

/** pickNotEqual draws every matching value other than s, about equally. */
TEST_F(TestTheoryWhiteBvLsDomain, pickNotEqual_exhaustive)
{
  for (uint32_t w = 1; w <= kMaxWidth; ++w)
  {
    for (const TernaryDomain& x : allDomains(w))
    {
      std::vector<uint32_t> m = matching(x);
      for (uint32_t s = 0; s < (1u << w); ++s)
      {
        std::vector<uint32_t> expected;
        for (uint32_t v : m)
        {
          if (v != s)
          {
            expected.push_back(v);
          }
        }
        if (expected.empty())
        {
          continue;  // x is fixed to s
        }
        std::stringstream ctx;
        ctx << x << " s=" << s;
        LsValue sv(w, s);
        std::map<uint32_t, uint32_t> counts;
        uint32_t draws = w <= 3 ? kDraws * expected.size() : 64;
        for (uint32_t i = 0; i < draws; ++i)
        {
          LsValue v = pickNotEqual(x, sv, d_rng);
          ASSERT_EQ(v.getSize(), w);
          ASSERT_TRUE(x.matches(v)) << ctx.str() << " v=" << v;
          ASSERT_NE(v, sv) << ctx.str();
          ++counts[toUint(v)];
        }
        if (w <= 3)
        {
          checkUniform(counts, expected, ctx.str());
        }
      }
    }
  }
}

/**
 * Without fixed bits the pick functions are the LsRng functions, with the
 * same random draws: this is what keeps a run without constant bits
 * identical to the base local search.
 */
TEST_F(TestTheoryWhiteBvLsDomain, pick_full_matches_rng)
{
  for (uint32_t w : {1u, 2u, 7u, 64u, 65u, 130u})
  {
    TernaryDomain x = TernaryDomain::full(w);
    LsRng r1(7);
    LsRng r2(7);
    for (uint32_t i = 0; i < 200; ++i)
    {
      ASSERT_EQ(pick(x, r1), r2.randomValue(w));
      LsValue a = r1.randomValue(w);
      LsValue b = r1.randomValue(w);
      r2.randomValue(w);
      r2.randomValue(w);
      if (b.unsignedLessThan(a))
      {
        std::swap(a, b);
      }
      ASSERT_EQ(pick(x, a, b, r1), r2.randomInRange(a, b));
      ASSERT_EQ(pickNotEqual(x, a, r1), r2.randomNotEqual(a));
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Wide values                                                                */
/* -------------------------------------------------------------------------- */

/**
 * Widths above 64 take a different code path. A domain d1 o p o d2 with two
 * small domains around a fixed pattern p of 70 bits has few matching values,
 * so the functions can be compared with brute force over them.
 */
TEST_F(TestTheoryWhiteBvLsDomain, wide)
{
  const uint32_t ws = 2;
  const uint32_t wp = 70;
  LsValue p = d_rng.randomValue(wp);
  while (isZero(p) || isOnes(p))
  {
    p = d_rng.randomValue(wp);
  }
  std::vector<LsValue> middles = {
      p, dec(p), inc(p), LsValue::mkZero(wp), LsValue::mkOnes(wp)};
  std::vector<TernaryDomain> doms = allDomains(ws);
  for (const TernaryDomain& d1 : doms)
  {
    for (const TernaryDomain& d2 : doms)
    {
      TernaryDomain x = concatD(d1, concatD(TernaryDomain::fixed(p), d2));
      ASSERT_EQ(x.getSize(), 2 * ws + wp);
      ASSERT_EQ(x.numFree(), d1.numFree() + d2.numFree());
      ASSERT_EQ(TernaryDomain::fromString(x.toString()), x);

      // The matching values, in increasing order.
      std::vector<LsValue> m;
      for (uint32_t v1 : matching(d1))
      {
        for (uint32_t v2 : matching(d2))
        {
          m.push_back(LsValue(ws, v1).concat(p).concat(LsValue(ws, v2)));
        }
      }
      for (size_t i = 0; i < m.size(); ++i)
      {
        ASSERT_TRUE(x.matches(m[i])) << x;
        ASSERT_TRUE(i == 0 || m[i - 1].unsignedLessThan(m[i])) << x;
        if (!x.isFixed())
        {
          ASSERT_EQ(compress(x, m[i]), LsValue(x.numFree(), i)) << x;
          ASSERT_EQ(expand(x, LsValue(x.numFree(), i)), m[i]) << x;
        }
      }
      ASSERT_EQ(x.lo(), m.front());
      ASSERT_EQ(x.hi(), m.back());

      for (uint32_t u1 = 0; u1 < (1u << ws); ++u1)
      {
        for (uint32_t u2 = 0; u2 < (1u << ws); ++u2)
        {
          for (const LsValue& q : middles)
          {
            LsValue a = LsValue(ws, u1).concat(q).concat(LsValue(ws, u2));
            ASSERT_EQ(x.matches(a),
                      q == p && d1.matches(LsValue(ws, u1))
                          && d2.matches(LsValue(ws, u2)));
            ASSERT_TRUE(x.matches(x.apply(a)));

            std::optional<LsValue> geq;
            std::optional<LsValue> leq;
            for (const LsValue& v : m)
            {
              if (!v.unsignedLessThan(a) && !geq)
              {
                geq = v;
              }
              if (v.unsignedLessThanEq(a))
              {
                leq = v;
              }
            }
            ASSERT_EQ(minMatchingGeq(x, a), geq) << x << " a=" << a;
            ASSERT_EQ(maxMatchingLeq(x, a), leq) << x << " b=" << a;

            // Ranges from a to the largest value, and from 0 to a.
            LsValue zero = LsValue::mkZero(x.getSize());
            LsValue ones = LsValue::mkOnes(x.getSize());
            ASSERT_EQ(hasMatchingIn(x, a, ones), geq.has_value());
            ASSERT_EQ(hasMatchingIn(x, zero, a), leq.has_value());
            if (geq)
            {
              size_t expected = 0;
              for (const LsValue& v : m)
              {
                expected += !v.unsignedLessThan(a);
              }
              // Enough draws to see every value, for some of the ranges.
              bool coverage = u2 == 0;
              std::set<std::string> seen;
              for (size_t i = 0, n = coverage ? 24 * expected : 8; i < n; ++i)
              {
                LsValue v = pick(x, a, ones, d_rng);
                ASSERT_TRUE(x.matches(v) && !v.unsignedLessThan(a));
                seen.insert(v.toString());
              }
              if (coverage)
              {
                ASSERT_EQ(seen.size(), expected) << x << " a=" << a;
              }
            }
            if (!x.isFixed() || x.lo() != a)
            {
              for (uint32_t i = 0; i < 16; ++i)
              {
                LsValue v = pickNotEqual(x, a, d_rng);
                ASSERT_TRUE(x.matches(v) && v != a) << x << " s=" << a;
              }
            }
          }
        }
      }
      LsValue v = pick(x, d_rng);
      ASSERT_TRUE(x.matches(v));
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
