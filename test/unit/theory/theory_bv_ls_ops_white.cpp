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
#include <sstream>
#include <vector>

#include "test.h"
#include "theory/bv/ls/ls_ops.h"
#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {

using namespace theory::bv::ls;

namespace test {

/** Exemptions from the completeness checks of checkRules. */
struct Exempt
{
  /** Inverse values need not cover every solution. */
  bool inverseCoverage = false;
  /** Consistent values need not cover every consistent value. */
  bool consistentCoverage = false;
};

class TestTheoryWhiteBvLsOps : public TestInternal
{
 protected:
  /** Evaluate op on the given children values. */
  static LsValue eval(const OpInfo& op, const std::vector<LsValue>& vals)
  {
    std::vector<const LsValue*> ch;
    for (const LsValue& v : vals)
    {
      ch.push_back(&v);
    }
    return evaluate(op, ch);
  }

  /**
   * Reference semantics of the binary operators of equal operand widths, on
   * plain integers. Operands are w-bit values with w <= 16.
   */
  static uint32_t refBinary(LsKind k, uint32_t w, uint32_t a, uint32_t b)
  {
    uint32_t mask = (1u << w) - 1;
    switch (k)
    {
      case LsKind::AND: return a & b;
      case LsKind::EQ: return a == b;
      case LsKind::ULT: return a < b;
      case LsKind::ADD: return (a + b) & mask;
      case LsKind::MUL: return (a * b) & mask;
      case LsKind::UDIV: return b == 0 ? mask : a / b;
      case LsKind::UREM: return b == 0 ? a : a % b;
      case LsKind::SHL: return b >= w ? 0 : (a << b) & mask;
      case LsKind::LSHR: return b >= w ? 0 : a >> b;
      default: break;
    }
    Unreachable();
  }

  /** Number of samples per soundness check. */
  static constexpr uint32_t kSamples = 64;
  /** Number of samples per coverage check. */
  static constexpr uint32_t kCoverageSamples = 256;
  /** Maximum width of x for the coverage checks. */
  static constexpr uint32_t kCoverageWidth = 3;

  /**
   * Check the rules of op for child posX exhaustively, with the children of
   * the given widths. For every target value t and every assignment of the
   * children (including the current value of x), compare isInvertible with a
   * brute-force search over x, check that inverse values produce t and that
   * consistent values have some assignment of the other children producing
   * t. For widths of x up to kCoverageWidth, also check that the sampled
   * values cover all solutions.
   */
  void checkRules(const OpInfo& op,
                  uint32_t posX,
                  const std::vector<uint32_t>& widths,
                  Exempt exempt = {})
  {
    uint32_t n = widths.size();
    uint32_t wx = widths[posX];
    // All assignments to the children, in mixed radix.
    std::vector<std::vector<LsValue>> assignments;
    std::vector<uint32_t> digits(n, 0);
    while (true)
    {
      std::vector<LsValue> vals;
      for (uint32_t i = 0; i < n; ++i)
      {
        vals.emplace_back(widths[i], digits[i]);
      }
      assignments.push_back(vals);
      uint32_t i = 0;
      while (i < n && ++digits[i] == (1u << widths[i]))
      {
        digits[i++] = 0;
      }
      if (i == n)
      {
        break;
      }
    }
    uint32_t wt = eval(op, assignments[0]).getSize();

    for (uint32_t tv = 0; tv < (1u << wt); ++tv)
    {
      LsValue t(wt, tv);
      // x' is consistent iff some assignment with x = x' produces t.
      std::set<uint32_t> consistent;
      for (const std::vector<LsValue>& vals : assignments)
      {
        if (eval(op, vals) == t)
        {
          consistent.insert(vals[posX].getValue().getUnsignedInt());
        }
      }

      for (const std::vector<LsValue>& vals : assignments)
      {
        std::vector<const LsValue*> ch;
        for (const LsValue& v : vals)
        {
          ch.push_back(&v);
        }
        std::stringstream ctx;
        ctx << op.kind << "[" << op.hi << ":" << op.lo << "] pos=" << posX
            << " t=" << t;
        for (uint32_t i = 0; i < n; ++i)
        {
          ctx << " ch" << i << "=" << vals[i];
        }

        // The solutions x' for the current values of the other children.
        std::set<uint32_t> solutions;
        for (uint32_t xv = 0; xv < (1u << wx); ++xv)
        {
          std::vector<LsValue> valsx = vals;
          valsx[posX] = LsValue(wx, xv);
          if (eval(op, valsx) == t)
          {
            solutions.insert(xv);
          }
        }
        bool expectedIc = !solutions.empty();
        if (op.kind == LsKind::ITE && posX > 0
            && vals[0].isBitSet(0) != (posX == 1))
        {
          // The disabled branch counts as not invertible.
          expectedIc = false;
        }
        ASSERT_EQ(isInvertible(op, posX, t, ch), expectedIc) << ctx.str();

        bool coverage = wx <= kCoverageWidth;
        if (expectedIc)
        {
          std::set<uint32_t> seen;
          uint32_t samples = coverage ? kCoverageSamples : kSamples;
          for (uint32_t i = 0; i < samples; ++i)
          {
            LsValue x = inverseValue(op, posX, t, ch, d_rng);
            ASSERT_EQ(x.getSize(), wx) << ctx.str();
            uint32_t xv = x.getValue().getUnsignedInt();
            ASSERT_TRUE(solutions.count(xv)) << ctx.str() << " inverse=" << x;
            seen.insert(xv);
          }
          if (coverage && !exempt.inverseCoverage)
          {
            ASSERT_EQ(seen, solutions) << ctx.str() << " (inverse coverage)";
          }
        }

        std::set<uint32_t> seen;
        uint32_t samples = coverage ? kCoverageSamples : kSamples;
        for (uint32_t i = 0; i < samples; ++i)
        {
          LsValue x = consistentValue(op, posX, t, ch, d_rng);
          ASSERT_EQ(x.getSize(), wx) << ctx.str();
          uint32_t xv = x.getValue().getUnsignedInt();
          ASSERT_TRUE(consistent.count(xv)) << ctx.str() << " consistent=" << x;
          seen.insert(xv);
        }
        if (coverage && !exempt.consistentCoverage)
        {
          ASSERT_EQ(seen, consistent) << ctx.str() << " (consistent coverage)";
        }
      }
    }
  }

  LsRng d_rng{42};
};

TEST_F(TestTheoryWhiteBvLsOps, arity_toString)
{
  ASSERT_EQ(arity(LsKind::CONST), 0u);
  ASSERT_EQ(arity(LsKind::VAR), 0u);
  ASSERT_EQ(arity(LsKind::NOT), 1u);
  ASSERT_EQ(arity(LsKind::EXTRACT), 1u);
  ASSERT_EQ(arity(LsKind::CONCAT), 2u);
  ASSERT_EQ(arity(LsKind::ULT), 2u);
  ASSERT_EQ(arity(LsKind::ITE), 3u);
  std::stringstream ss;
  ss << LsKind::LSHR;
  ASSERT_EQ(ss.str(), "LSHR");
}

/** All binary operators of equal operand widths, exhaustive for w <= 4. */
TEST_F(TestTheoryWhiteBvLsOps, evaluate_binary_exhaustive)
{
  for (LsKind k : {LsKind::AND,
                   LsKind::EQ,
                   LsKind::ULT,
                   LsKind::ADD,
                   LsKind::MUL,
                   LsKind::UDIV,
                   LsKind::UREM,
                   LsKind::SHL,
                   LsKind::LSHR})
  {
    bool isPred = k == LsKind::EQ || k == LsKind::ULT;
    for (uint32_t w = 1; w <= 4; ++w)
    {
      for (uint32_t a = 0; a < (1u << w); ++a)
      {
        for (uint32_t b = 0; b < (1u << w); ++b)
        {
          LsValue r = eval({k}, {LsValue(w, a), LsValue(w, b)});
          LsValue expected(isPred ? 1 : w, refBinary(k, w, a, b));
          ASSERT_EQ(r, expected) << k << " w=" << w << " a=" << a << " b=" << b;
        }
      }
    }
  }
}

/** NOT, CONCAT, EXTRACT and ITE, exhaustive for widths <= 4. */
TEST_F(TestTheoryWhiteBvLsOps, evaluate_other_exhaustive)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    uint32_t mask = (1u << w) - 1;
    for (uint32_t a = 0; a <= mask; ++a)
    {
      ASSERT_EQ(eval({LsKind::NOT}, {LsValue(w, a)}), LsValue(w, ~a & mask));

      for (uint32_t hi = 0; hi < w; ++hi)
      {
        for (uint32_t lo = 0; lo <= hi; ++lo)
        {
          uint32_t width = hi - lo + 1;
          LsValue r = eval({LsKind::EXTRACT, hi, lo}, {LsValue(w, a)});
          ASSERT_EQ(r, LsValue(width, (a >> lo) & ((1u << width) - 1)))
              << "w=" << w << " a=" << a << " [" << hi << ":" << lo << "]";
        }
      }

      for (uint32_t wb = 1; wb <= 4; ++wb)
      {
        for (uint32_t b = 0; b < (1u << wb); ++b)
        {
          // The first child is the most significant part.
          LsValue r = eval({LsKind::CONCAT}, {LsValue(w, a), LsValue(wb, b)});
          ASSERT_EQ(r, LsValue(w + wb, (a << wb) | b))
              << "w=" << w << " a=" << a << " wb=" << wb << " b=" << b;
        }
      }

      for (uint32_t b = 0; b <= mask; ++b)
      {
        for (uint32_t c = 0; c <= 1; ++c)
        {
          LsValue r = eval({LsKind::ITE},
                           {LsValue(1, c), LsValue(w, a), LsValue(w, b)});
          ASSERT_EQ(r, LsValue(w, c ? a : b));
        }
      }
    }
  }
}

/** Values wider than 64 bits, on cases with known results. */
TEST_F(TestTheoryWhiteBvLsOps, evaluate_wide)
{
  for (uint32_t w : {65u, 128u, 1000u})
  {
    LsValue zero = LsValue::mkZero(w);
    LsValue one = LsValue::mkOne(w);
    LsValue ones = LsValue::mkOnes(w);
    LsValue msbOnly = LsValue::mkMinSigned(w);
    LsValue lo64 = LsValue(w, Integer(2).pow(64) - 1);  // bits [63:0] set
    LsValue bit64 = LsValue(w, Integer(2).pow(64));
    LsValue t = LsValue::mkOne(1), f = LsValue::mkZero(1);

    ASSERT_EQ(eval({LsKind::NOT}, {zero}), ones);
    ASSERT_EQ(eval({LsKind::AND}, {ones, lo64}), lo64);
    ASSERT_EQ(eval({LsKind::EQ}, {lo64, lo64}), t);
    ASSERT_EQ(eval({LsKind::EQ}, {lo64, bit64}), f);
    ASSERT_EQ(eval({LsKind::ULT}, {lo64, bit64}), t);
    ASSERT_EQ(eval({LsKind::ULT}, {ones, msbOnly}), f);
    // The carry crosses the 64-bit word boundary, and ones + 1 wraps.
    ASSERT_EQ(eval({LsKind::ADD}, {lo64, one}), bit64);
    ASSERT_EQ(eval({LsKind::ADD}, {ones, one}), zero);
    // ones * ones = 1 (mod 2^w).
    ASSERT_EQ(eval({LsKind::MUL}, {ones, ones}), one);
    ASSERT_EQ(eval({LsKind::UDIV}, {bit64, lo64}), one);
    ASSERT_EQ(eval({LsKind::UDIV}, {lo64, zero}), ones);
    ASSERT_EQ(eval({LsKind::UREM}, {bit64, lo64}), one);
    ASSERT_EQ(eval({LsKind::UREM}, {lo64, zero}), lo64);
    ASSERT_EQ(eval({LsKind::SHL}, {one, LsValue(w, 64u)}), bit64);
    ASSERT_EQ(eval({LsKind::SHL}, {ones, LsValue(w, w)}), zero);
    ASSERT_EQ(eval({LsKind::SHL}, {ones, ones}), zero);
    ASSERT_EQ(eval({LsKind::LSHR}, {bit64, LsValue(w, 64u)}), one);
    ASSERT_EQ(eval({LsKind::LSHR}, {ones, ones}), zero);
    ASSERT_EQ(eval({LsKind::EXTRACT, 64, 63}, {bit64}), LsValue(2, 2u));
    ASSERT_EQ(eval({LsKind::EXTRACT, w - 1, w - 1}, {msbOnly}), t);
    LsValue cat = eval({LsKind::CONCAT}, {one, lo64});
    ASSERT_EQ(cat.getSize(), 2 * w);
    ASSERT_EQ(cat.extract(w - 1, 0), lo64);
    ASSERT_EQ(cat.extract(2 * w - 1, w), one);
    ASSERT_EQ(eval({LsKind::ITE}, {t, lo64, bit64}), lo64);
    ASSERT_EQ(eval({LsKind::ITE}, {f, lo64, bit64}), bit64);
  }
}

/* -------------------------------------------------------------------------- */
/* Invertibility conditions, inverse and consistent values                    */
/* -------------------------------------------------------------------------- */

TEST_F(TestTheoryWhiteBvLsOps, rules_not)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::NOT}, 0, {w}));
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_and_eq_add)
{
  for (LsKind k : {LsKind::AND, LsKind::EQ, LsKind::ADD})
  {
    for (uint32_t w = 1; w <= 4; ++w)
    {
      for (uint32_t pos = 0; pos <= 1; ++pos)
      {
        ASSERT_NO_FATAL_FAILURE(checkRules({k}, pos, {w, w}));
      }
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_concat)
{
  for (uint32_t w0 = 1; w0 <= 3; ++w0)
  {
    for (uint32_t w1 = 1; w1 <= 3; ++w1)
    {
      for (uint32_t pos = 0; pos <= 1; ++pos)
      {
        ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::CONCAT}, pos, {w0, w1}));
      }
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_extract)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    for (uint32_t hi = 0; hi < w; ++hi)
    {
      for (uint32_t lo = 0; lo <= hi; ++lo)
      {
        ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::EXTRACT, hi, lo}, 0, {w}));
      }
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_ite)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::ITE}, 0, {1, w, w}));
    // The consistent value of a branch is always t, as in Bitwuzla, although
    // any value is consistent (with the condition selecting the other branch).
    Exempt exempt;
    exempt.consistentCoverage = true;
    for (uint32_t pos = 1; pos <= 2; ++pos)
    {
      ASSERT_NO_FATAL_FAILURE(
          checkRules({LsKind::ITE}, pos, {1, w, w}, exempt));
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_ult)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    for (uint32_t pos = 0; pos <= 1; ++pos)
    {
      ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::ULT}, pos, {w, w}));
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, rules_shl_lshr)
{
  for (LsKind k : {LsKind::SHL, LsKind::LSHR})
  {
    for (uint32_t w = 1; w <= 4; ++w)
    {
      for (uint32_t pos = 0; pos <= 1; ++pos)
      {
        ASSERT_NO_FATAL_FAILURE(checkRules({k}, pos, {w, w}));
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
