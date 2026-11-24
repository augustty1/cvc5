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

#include <optional>
#include <set>
#include <sstream>
#include <vector>

#include "test.h"
#include "theory/bv/ls/ls_domain.h"
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
    LsChildren ch;
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
  /** In a sampled check, about one case in kSampleRate is checked. */
  static constexpr uint32_t kSampleRate = 16;

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
          consistent.insert(vals[posX].toInteger().getUnsignedInt());
        }
      }

      for (const std::vector<LsValue>& vals : assignments)
      {
        LsChildren ch;
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
            uint32_t xv = x.toInteger().getUnsignedInt();
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
          uint32_t xv = x.toInteger().getUnsignedInt();
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

  /** All assignments to children of the given widths. */
  static std::vector<std::vector<LsValue>> allAssignments(
      const std::vector<uint32_t>& widths)
  {
    uint32_t n = widths.size();
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
    return assignments;
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

  /** All combinations of domains for children of the given widths. */
  static std::vector<std::vector<TernaryDomain>> allDomainTuples(
      const std::vector<uint32_t>& widths)
  {
    std::vector<std::vector<TernaryDomain>> res = {{}};
    for (uint32_t w : widths)
    {
      std::vector<std::vector<TernaryDomain>> next;
      for (const std::vector<TernaryDomain>& prefix : res)
      {
        for (const TernaryDomain& d : allDomains(w))
        {
          next.push_back(prefix);
          next.back().push_back(d);
        }
      }
      res = std::move(next);
    }
    return res;
  }

  /**
   * Operators with the widths of their children, for the tests that go over
   * all operators: every kind at operand width w, EXTRACT with every pair of
   * indices, and CONCAT also with operands of different widths.
   */
  static std::vector<std::pair<OpInfo, std::vector<uint32_t>>> allOps(
      uint32_t w)
  {
    std::vector<std::pair<OpInfo, std::vector<uint32_t>>> res;
    res.push_back({{LsKind::NOT}, {w}});
    for (LsKind k : {LsKind::AND,
                     LsKind::EQ,
                     LsKind::ULT,
                     LsKind::ADD,
                     LsKind::MUL,
                     LsKind::UDIV,
                     LsKind::UREM,
                     LsKind::SHL,
                     LsKind::LSHR,
                     LsKind::CONCAT})
    {
      res.push_back({{k}, {w, w}});
    }
    if (w > 1)
    {
      res.push_back({{LsKind::CONCAT}, {1, w}});
      res.push_back({{LsKind::CONCAT}, {w, 1}});
    }
    for (uint32_t hi = 0; hi < w; ++hi)
    {
      for (uint32_t lo = 0; lo <= hi; ++lo)
      {
        res.push_back({{LsKind::EXTRACT, hi, lo}, {w}});
      }
    }
    res.push_back({{LsKind::ITE}, {1, w, w}});
    return res;
  }

  /**
   * Check the rules modulo constant bits of op for child posX against brute
   * force, for every domain x of that child with a fixed bit, every target t
   * and every assignment of the children in which the value of the child
   * matches x:
   *  - isInvertible(op, posX, t, ch, x) holds iff some value matching x is a
   *    solution, i.e., produces t with the other children fixed (always
   *    false for the disabled branch of an ITE);
   *  - inverse values are solutions that match x (plan R1);
   *  - tryConsistentValue returns a value iff some value matching x is
   *    consistent, i.e., produces t with some values of the other children,
   *    and it returns such a value (for a branch of an ITE the consistent
   *    value is t, iff it matches x, plan D11);
   *  - if x has at most kCoverageWidth bits, the inverse values cover all
   *    solutions and the consistent values all consistent values that match
   *    x (plan R2, R3).
   * If sampled, about one case in kSampleRate is checked, with kSamples
   * draws and no coverage check.
   */
  void checkRulesDomains(const OpInfo& op,
                         uint32_t posX,
                         const std::vector<uint32_t>& widths,
                         bool sampled)
  {
    uint32_t wx = widths[posX];
    std::vector<std::vector<LsValue>> assignments = allAssignments(widths);
    uint32_t wt = eval(op, assignments[0]).getSize();
    bool iteBranch = op.kind == LsKind::ITE && posX > 0;
    bool coverage = !sampled && wx <= kCoverageWidth;
    uint32_t samples = coverage ? kCoverageSamples : kSamples;
    // Selects the sampled cases, independently of the rules' draws.
    LsRng select(31 * wx + posX);
    for (uint32_t tv = 0; tv < (1u << wt); ++tv)
    {
      LsValue t(wt, tv);
      // The consistent values of x, ignoring its domain.
      std::set<uint32_t> consistentAll;
      for (const std::vector<LsValue>& vals : assignments)
      {
        if (eval(op, vals) == t)
        {
          consistentAll.insert(vals[posX].toInteger().getUnsignedInt());
        }
      }
      for (const TernaryDomain& x : allDomains(wx))
      {
        if (!x.hasFixedBits())
        {
          continue;  // the base rules, see full_domain_is_base
        }
        std::set<uint32_t> consistent;
        for (uint32_t v : consistentAll)
        {
          if (x.matches(LsValue(wx, v)))
          {
            consistent.insert(v);
          }
        }
        if (iteBranch)
        {
          consistent.clear();
          if (x.matches(t))
          {
            consistent.insert(tv);
          }
        }
        for (const std::vector<LsValue>& vals : assignments)
        {
          if (!x.matches(vals[posX])
              || (sampled && select.pickIndex(kSampleRate) != 0))
          {
            continue;
          }
          LsChildren ch;
          for (const LsValue& v : vals)
          {
            ch.push_back(&v);
          }
          std::stringstream ctx;
          ctx << opToString(op, widths) << " pos=" << posX << " x=" << x
              << " t=" << t;
          for (uint32_t i = 0; i < vals.size(); ++i)
          {
            ctx << " ch" << i << "=" << vals[i];
          }

          std::set<uint32_t> solutions;
          for (uint32_t xv = 0; xv < (1u << wx); ++xv)
          {
            std::vector<LsValue> valsx = vals;
            valsx[posX] = LsValue(wx, xv);
            if (x.matches(valsx[posX]) && eval(op, valsx) == t)
            {
              solutions.insert(xv);
            }
          }
          bool expectedIc = !solutions.empty();
          if (iteBranch && vals[0].isBitSet(0) != (posX == 1))
          {
            expectedIc = false;  // the disabled branch
          }
          ASSERT_EQ(isInvertible(op, posX, t, ch, x), expectedIc) << ctx.str();
          if (expectedIc)
          {
            std::set<uint32_t> seen;
            for (uint32_t i = 0; i < samples; ++i)
            {
              LsValue v = inverseValue(op, posX, t, ch, x, d_rng);
              ASSERT_EQ(v.getSize(), wx) << ctx.str();
              uint32_t vv = v.toInteger().getUnsignedInt();
              ASSERT_TRUE(solutions.count(vv)) << ctx.str() << " inverse=" << v;
              seen.insert(vv);
            }
            if (coverage)
            {
              ASSERT_EQ(seen, solutions) << ctx.str() << " (inverse coverage)";
            }
          }

          std::set<uint32_t> seen;
          for (uint32_t i = 0; i < samples; ++i)
          {
            std::optional<LsValue> v =
                tryConsistentValue(op, posX, t, ch, x, d_rng);
            ASSERT_EQ(v.has_value(), !consistent.empty()) << ctx.str();
            if (!v)
            {
              break;
            }
            ASSERT_EQ(v->getSize(), wx) << ctx.str();
            uint32_t vv = v->toInteger().getUnsignedInt();
            ASSERT_TRUE(consistent.count(vv))
                << ctx.str() << " consistent=" << *v;
            seen.insert(vv);
          }
          if (coverage)
          {
            ASSERT_EQ(seen, consistent)
                << ctx.str() << " (consistent coverage)";
          }
        }
      }
    }
  }

  static std::string opToString(const OpInfo& op,
                                const std::vector<uint32_t>& widths)
  {
    std::stringstream ss;
    ss << op.kind;
    if (op.kind == LsKind::EXTRACT)
    {
      ss << "[" << op.hi << ":" << op.lo << "]";
    }
    ss << " widths";
    for (uint32_t w : widths)
    {
      ss << " " << w;
    }
    return ss.str();
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

TEST_F(TestTheoryWhiteBvLsOps, rules_mul_udiv)
{
  for (LsKind k : {LsKind::MUL, LsKind::UDIV})
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

TEST_F(TestTheoryWhiteBvLsOps, rules_urem)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    for (uint32_t pos = 0; pos <= 1; ++pos)
    {
      ASSERT_NO_FATAL_FAILURE(checkRules({LsKind::UREM}, pos, {w, w}));
    }
  }
}

TEST_F(TestTheoryWhiteBvLsOps, is_essential)
{
  // (op, widths of the children) to check, all positions each.
  std::vector<std::pair<OpInfo, std::vector<uint32_t>>> cases;
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
    for (uint32_t w = 1; w <= 3; ++w)
    {
      cases.push_back({{k}, {w, w}});
    }
  }
  cases.push_back({{LsKind::CONCAT}, {1, 2}});
  cases.push_back({{LsKind::CONCAT}, {2, 1}});
  cases.push_back({{LsKind::ITE}, {1, 2, 2}});

  for (const auto& [op, widths] : cases)
  {
    uint32_t n = widths.size();
    std::vector<uint32_t> digits(n, 0);
    while (true)
    {
      std::vector<LsValue> vals;
      for (uint32_t i = 0; i < n; ++i)
      {
        vals.emplace_back(widths[i], digits[i]);
      }
      LsChildren ch;
      for (const LsValue& v : vals)
      {
        ch.push_back(&v);
      }
      uint32_t wt = eval(op, vals).getSize();
      for (uint32_t tv = 0; tv < (1u << wt); ++tv)
      {
        LsValue t(wt, tv);
        // canReach[j]: some value of child j alone produces t.
        std::vector<bool> canReach(n, false);
        for (uint32_t j = 0; j < n; ++j)
        {
          bool disabled = op.kind == LsKind::ITE && j > 0
                          && vals[0].isBitSet(0) != (j == 1);
          for (uint32_t xv = 0; !disabled && xv < (1u << widths[j]); ++xv)
          {
            std::vector<LsValue> valsx = vals;
            valsx[j] = LsValue(widths[j], xv);
            if (eval(op, valsx) == t)
            {
              canReach[j] = true;
              break;
            }
          }
        }
        for (uint32_t i = 0; i < n; ++i)
        {
          bool expected = true;
          for (uint32_t j = 0; j < n; ++j)
          {
            expected = expected && (j == i || !canReach[j]);
          }
          ASSERT_EQ(isEssential(op, i, t, ch), expected)
              << op.kind << " i=" << i << " t=" << t << " ch0=" << vals[0]
              << " ch1=" << vals[1];
        }
      }
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
  }
  // Unary operators: the only input is essential.
  LsValue x(4, 5u);
  ASSERT_TRUE(isEssential({LsKind::NOT}, 0, ~x, {&x}));
  ASSERT_TRUE(isEssential({LsKind::EXTRACT, 2, 1}, 0, LsValue(2, 1u), {&x}));
}

TEST_F(TestTheoryWhiteBvLsOps, rules_wide)
{
  // Widths across 64-bit word boundaries, which the exhaustive tests do not
  // reach. t is produced from random children, so position posX is
  // invertible. A consistent value x' is checked through the IC of the other
  // position: some s' produces t with x' iff it holds.
  for (uint32_t w : {31u, 32u, 33u, 63u, 64u, 65u, 128u})
  {
    for (LsKind k : {LsKind::MUL, LsKind::UDIV, LsKind::UREM})
    {
      for (uint32_t pos = 0; pos <= 1; ++pos)
      {
        for (uint32_t i = 0; i < 200; ++i)
        {
          // Small values make the special cases (0, 1, divisors) likely.
          auto draw = [&]() {
            uint32_t r = d_rng.pickIndex(4);
            if (r == 0) return LsValue(w, d_rng.pickIndex(4));
            if (r == 1)
              return LsValue::mkOnes(w) - LsValue(w, d_rng.pickIndex(3));
            return d_rng.randomValue(w);
          };
          LsValue a = draw();
          LsValue b = draw();
          LsChildren ch = {&a, &b};
          LsValue t = eval({k}, {a, b});
          std::stringstream ctx;
          ctx << k << " w=" << w << " pos=" << pos << " a=" << a << " b=" << b;
          ASSERT_TRUE(isInvertible({k}, pos, t, ch)) << ctx.str();
          LsValue x = inverseValue({k}, pos, t, ch, d_rng);
          std::vector<LsValue> vals = {a, b};
          vals[pos] = x;
          ASSERT_EQ(eval({k}, vals), t) << ctx.str() << " inverse=" << x;

          // A random target, not necessarily reachable.
          LsValue t2 = draw();
          LsValue c = consistentValue({k}, pos, t2, ch, d_rng);
          LsChildren chc = ch;
          chc[pos] = &c;
          ASSERT_TRUE(isInvertible({k}, 1 - pos, t2, chc))
              << ctx.str() << " t=" << t2 << " consistent=" << c;
          if (isInvertible({k}, pos, t2, ch))
          {
            LsValue y = inverseValue({k}, pos, t2, ch, d_rng);
            vals = {a, b};
            vals[pos] = y;
            ASSERT_EQ(eval({k}, vals), t2) << ctx.str() << " inverse=" << y;
          }
        }
      }
    }
  }
}

/* -------------------------------------------------------------------------- */
/* Rules modulo constant bits                                                 */
/* -------------------------------------------------------------------------- */

/**
 * With a domain without fixed bits, the rules modulo constant bits are the
 * base rules: same results and same random draws. This is what keeps a run
 * without constant bits identical to the base local search.
 */
TEST_F(TestTheoryWhiteBvLsOps, full_domain_is_base)
{
  for (uint32_t w = 1; w <= 3; ++w)
  {
    for (const auto& [op, widths] : allOps(w))
    {
      uint32_t n = widths.size();
      std::vector<TernaryDomain> full;
      for (uint32_t wi : widths)
      {
        full.push_back(TernaryDomain::full(wi));
      }
      LsDomains doms;
      for (const TernaryDomain& d : full)
      {
        doms.push_back(&d);
      }
      std::vector<std::vector<LsValue>> assignments = allAssignments(widths);
      uint32_t wt = eval(op, assignments[0]).getSize();
      // Two generators in the same state: they stay so as long as both
      // variants of a rule make the same draws.
      LsRng r1(w);
      LsRng r2(w);
      for (uint32_t tv = 0; tv < (1u << wt); ++tv)
      {
        LsValue t(wt, tv);
        for (const std::vector<LsValue>& vals : assignments)
        {
          LsChildren ch;
          for (const LsValue& v : vals)
          {
            ch.push_back(&v);
          }
          for (uint32_t pos = 0; pos < n; ++pos)
          {
            std::stringstream ctx;
            ctx << opToString(op, widths) << " pos=" << pos << " t=" << t;
            const TernaryDomain& x = full[pos];
            bool ic = isInvertible(op, pos, t, ch);
            ASSERT_EQ(isInvertible(op, pos, t, ch, x), ic) << ctx.str();
            ASSERT_EQ(isEssential(op, pos, t, ch, doms),
                      isEssential(op, pos, t, ch))
                << ctx.str();

            if (ic)
            {
              ASSERT_EQ(inverseValue(op, pos, t, ch, x, r1),
                        inverseValue(op, pos, t, ch, r2))
                  << ctx.str();
            }
            // Without fixed bits a consistent value always exists.
            std::optional<LsValue> c =
                tryConsistentValue(op, pos, t, ch, x, r1);
            ASSERT_TRUE(c.has_value()) << ctx.str();
            ASSERT_EQ(*c, consistentValue(op, pos, t, ch, r2)) << ctx.str();
            ASSERT_EQ(r1.randomValue(64), r2.randomValue(64)) << ctx.str();
          }
        }
      }
    }
  }
}

/**
 * The rules modulo constant bits of NOT, AND, EQ, ADD, CONCAT, EXTRACT and
 * ITE (goal 4 of Step 3) against brute force: every domain with a fixed bit
 * up to 3 bits, sampled at 4 bits.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_bitwise)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    bool sampled = w == 4;
    checkRulesDomains({LsKind::NOT}, 0, {w}, sampled);
    for (LsKind k : {LsKind::AND, LsKind::EQ, LsKind::ADD, LsKind::CONCAT})
    {
      for (uint32_t pos = 0; pos < 2; ++pos)
      {
        checkRulesDomains({k}, pos, {w, w}, sampled);
      }
    }
    if (w > 1)
    {
      for (uint32_t pos = 0; pos < 2; ++pos)
      {
        checkRulesDomains({LsKind::CONCAT}, pos, {1, w}, sampled);
        checkRulesDomains({LsKind::CONCAT}, pos, {w, 1}, sampled);
      }
    }
    for (uint32_t hi = 0; hi < w; ++hi)
    {
      for (uint32_t lo = 0; lo <= hi; ++lo)
      {
        checkRulesDomains({LsKind::EXTRACT, hi, lo}, 0, {w}, sampled);
      }
    }
    for (uint32_t pos = 0; pos < 3; ++pos)
    {
      checkRulesDomains({LsKind::ITE}, pos, {1, w, w}, sampled);
    }
  }
}

/**
 * forwardDomain is sound: the value of the operator matches it whenever the
 * values of the children match their domains. Where it is documented to be
 * exact, a bit is fixed iff it is the same for all those values.
 */
TEST_F(TestTheoryWhiteBvLsOps, forward_domain)
{
  for (uint32_t w = 1; w <= 3; ++w)
  {
    for (const auto& [op, widths] : allOps(w))
    {
      if (w == 3 && (op.kind == LsKind::ITE || widths.size() == 2))
      {
        // Width 3 only for the unary operators and for one cheap binary one.
        if (op.kind != LsKind::AND)
        {
          continue;
        }
      }
      std::vector<std::vector<LsValue>> assignments = allAssignments(widths);
      for (const std::vector<TernaryDomain>& ds : allDomainTuples(widths))
      {
        LsDomains doms;
        bool allFixed = true;
        std::stringstream ctx;
        ctx << opToString(op, widths) << " domains";
        for (const TernaryDomain& d : ds)
        {
          doms.push_back(&d);
          allFixed = allFixed && d.isFixed();
          ctx << " " << d;
        }
        TernaryDomain fd = forwardDomain(op, doms);
        ASSERT_TRUE(TernaryDomain::isValid(fd.lo(), fd.hi())) << ctx.str();

        // The values of the operator over the matching children values.
        std::set<uint32_t> image;
        for (const std::vector<LsValue>& vals : assignments)
        {
          bool match = true;
          for (size_t i = 0; i < vals.size(); ++i)
          {
            match = match && ds[i].matches(vals[i]);
          }
          if (match)
          {
            LsValue v = eval(op, vals);
            ASSERT_EQ(fd.getSize(), v.getSize()) << ctx.str();
            ASSERT_TRUE(fd.matches(v)) << ctx.str() << " value " << v;
            image.insert(v.toInteger().getUnsignedInt());
          }
        }

        bool exact = allFixed;
        switch (op.kind)
        {
          case LsKind::NOT:
          case LsKind::AND:
          case LsKind::CONCAT:
          case LsKind::EXTRACT:
          case LsKind::ITE: exact = true; break;
          case LsKind::SHL:
          case LsKind::LSHR: exact = exact || ds[1].isFixed(); break;
          default: break;
        }
        if (allFixed)
        {
          ASSERT_TRUE(fd.isFixed()) << ctx.str();
        }
        if (exact)
        {
          for (uint32_t i = 0; i < fd.getSize(); ++i)
          {
            bool all0 = true;
            bool all1 = true;
            for (uint32_t v : image)
            {
              (((v >> i) & 1) != 0 ? all0 : all1) = false;
            }
            ASSERT_EQ(fd.isFixedTrue(i), all1) << ctx.str() << " bit " << i;
            ASSERT_EQ(fd.isFixedFalse(i), all0) << ctx.str() << " bit " << i;
          }
        }
        else
        {
          ASSERT_FALSE(fd.hasFixedBits()) << ctx.str();
        }
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
