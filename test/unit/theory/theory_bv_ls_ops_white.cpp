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
 * The rules modulo constant bits of ULT, SHL and LSHR (goal 5 of Step 3)
 * against brute force: every domain with a fixed bit up to 3 bits, sampled
 * at 4 bits.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_ult_shifts)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    bool sampled = w == 4;
    for (LsKind k : {LsKind::ULT, LsKind::SHL, LsKind::LSHR})
    {
      for (uint32_t pos = 0; pos < 2; ++pos)
      {
        checkRulesDomains({k}, pos, {w, w}, sampled);
      }
    }
  }
}

/**
 * The rules modulo constant bits of MUL and UDIV (goal 6 of Step 3) against
 * brute force: every domain with a fixed bit up to 3 bits, sampled at 4
 * bits. Up to 4 bits the search of the UDIV consistent value at position 0
 * always ends within its step limit, so it is exact here.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_mul_udiv)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    bool sampled = w == 4;
    for (LsKind k : {LsKind::MUL, LsKind::UDIV})
    {
      for (uint32_t pos = 0; pos < 2; ++pos)
      {
        checkRulesDomains({k}, pos, {w, w}, sampled);
      }
    }
  }
}

/**
 * Return true if some s gives v / s = t at width w <= 32 (with v / 0 =
 * ones): for t = ones (s = 0); for t = 0 iff v != ones (s > v); otherwise
 * iff v mod t < v div t (s = v div t), which includes v = t.
 */
static bool udivConsistentRef(uint64_t v, uint64_t t, uint32_t w)
{
  uint64_t ones = (uint64_t(1) << w) - 1;
  if (t == ones)
  {
    return true;
  }
  if (t == 0)
  {
    return v != ones;
  }
  return v % t < v / t;
}

/**
 * The consistent value of x / s = t modulo constant bits at 16 bits, where
 * the bounded search of its stage 4 (plan, Sec. 3.4) can run out of steps.
 *
 * With t = 256 and the low byte of x fixed to 200, the consistent values
 * are the dividends of y >= 201: the search from y = 2 needs about 200
 * steps, more than its limit of 100. Stage 2 draws y in [2, 255] and finds
 * a value with probability 1 - (199/254)^20, about 0.99. So the result is
 * nothing in a few calls, which is not a wrong answer for ever: most calls
 * return a value (plan R2). In the version that only searched (v1), every
 * call returned nothing.
 *
 * On random domains and targets, every value returned matches x and is
 * consistent, and when a consistent value matching x exists, some call out
 * of 40 returns one.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_udiv_consistent_wide)
{
  const uint32_t w = 16;
  OpInfo udiv{LsKind::UDIV};
  for (uint32_t v = 0; v < 16; ++v)
  {
    for (uint32_t t = 0; t < 16; ++t)
    {
      bool exists = false;
      for (uint32_t sv = 0; sv < 16; ++sv)
      {
        exists = exists || refBinary(LsKind::UDIV, 4, v, sv) == t;
      }
      ASSERT_EQ(udivConsistentRef(v, t, 4), exists) << v << " " << t;
    }
  }

  {
    TernaryDomain x(LsValue(w, 200), LsValue(w, 0xffc8));
    LsValue t(w, 256);
    LsValue cur(w, 0x1000 + 200);
    LsValue s(w, 3);
    LsChildren ch{&cur, &s};
    uint32_t values = 0;
    uint32_t nothing = 0;
    for (uint32_t i = 0; i < 2000; ++i)
    {
      std::optional<LsValue> v = tryConsistentValue(udiv, 0, t, ch, x, d_rng);
      if (!v)
      {
        ++nothing;
        continue;
      }
      uint64_t vv = v->toInteger().getUnsignedLong();
      ASSERT_TRUE(x.matches(*v)) << *v;
      ASSERT_TRUE(udivConsistentRef(vv, 256, w)) << *v;
      ASSERT_GE(vv / 256, 201u) << *v;
      ++values;
    }
    ASSERT_GT(nothing, 0u);
    ASSERT_GT(values, 1900u);
  }

  LsRng gen(53);
  uint32_t withValue = 0;
  uint32_t without = 0;
  for (uint32_t r = 0; r < 300; ++r)
  {
    // Many fixed bits make the consistent values sparse; targets near 2^8
    // have the most runs of dividends.
    LsValue fixed = gen.randomValue(w) | gen.randomValue(w);
    LsValue bits = gen.randomValue(w) & fixed;
    TernaryDomain x(bits, bits | ~fixed);
    LsValue t = r % 3 == 0
                    ? gen.randomValue(w)
                    : LsValue(w, 2 + gen.pickIndex(r % 3 == 1 ? 30 : 600));
    uint64_t tv = t.toInteger().getUnsignedLong();
    uint64_t lo = x.lo().toInteger().getUnsignedLong();
    uint64_t hi = x.hi().toInteger().getUnsignedLong();
    bool exists = false;
    for (uint64_t v = 0; v < (uint64_t(1) << w) && !exists; ++v)
    {
      exists = (v & hi) == v && (v | lo) == v && udivConsistentRef(v, tv, w);
    }
    LsValue cur = x.apply(gen.randomValue(w));
    LsValue s = gen.randomValue(w);
    LsChildren ch{&cur, &s};
    std::stringstream ctx;
    ctx << "x=" << x << " t=" << t;
    uint32_t got = 0;
    for (uint32_t i = 0; i < 40; ++i)
    {
      std::optional<LsValue> v = tryConsistentValue(udiv, 0, t, ch, x, d_rng);
      if (!v)
      {
        continue;
      }
      ASSERT_TRUE(x.matches(*v)) << ctx.str() << " v=" << *v;
      ASSERT_TRUE(udivConsistentRef(v->toInteger().getUnsignedLong(), tv, w))
          << ctx.str() << " v=" << *v;
      ++got;
    }
    ASSERT_EQ(got > 0, exists) << ctx.str();
    ++(exists ? withValue : without);
  }
  // Both outcomes occur.
  ASSERT_GT(withValue, 50u);
  ASSERT_GT(without, 10u);
}

/**
 * The rules modulo constant bits of s mod x = t (UREM at position 1, goal 8
 * of Step 3) against brute force: every domain with a fixed bit up to 3 bits,
 * sampled at 4 bits. Up to 4 bits the bounded divisor search sees every
 * divisor, so the check is exact here.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_urem_divisors)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    checkRulesDomains({LsKind::UREM}, 1, {w, w}, w == 4);
  }
}

/**
 * s mod x = t at 16 bits, where the bounded divisor search (pairs (i, n / i)
 * for i <= 100, no factorization, plan D19) does not see every divisor of
 * n = s - t.
 *
 * With n = 2 * 101 * 103 = 20806 and t = 1, the search finds 2, 10403 and
 * 20806 but not 101, 103, 202 or 206. The inverse values still reach those
 * through the sampling stage, so every divisor has a non-zero probability
 * (plan R3).
 *
 * With n = 101 * 103 and x < 2^8, the only solutions are 101 and 103 (n does
 * not fit) and the search finds neither: the check says no, which plan D19
 * accepts. The step
 * then takes the consistent branch, whose values (0 and every x > t) include
 * them. With the factorization of v3 the check would say yes.
 *
 * On random domains and targets, the check never says yes wrongly, and the
 * inverse values are always divisors that match x.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_urem_divisors_wide)
{
  const uint32_t w = 16;
  OpInfo urem{LsKind::UREM};
  // x < 2^15: some fixed bit, so the rules modulo constant bits apply.
  TernaryDomain below15(LsValue::mkZero(w), LsValue(w, 0x7fff));
  {
    LsValue t(w, 1);
    LsValue s(w, 2 * 101 * 103 + 1);
    LsValue cur(w, 5);
    LsChildren ch{&s, &cur};
    ASSERT_TRUE(isInvertible(urem, 1, t, ch, below15));
    std::set<uint64_t> seen;
    for (uint32_t i = 0; i < 100000; ++i)
    {
      LsValue v = inverseValue(urem, 1, t, ch, below15, d_rng);
      uint64_t d = v.toInteger().getUnsignedLong();
      ASSERT_TRUE(d > 1 && 20806 % d == 0 && below15.matches(v)) << v;
      seen.insert(d);
    }
    ASSERT_TRUE(seen.count(2) && seen.count(10403) && seen.count(20806));
    bool missedByTheSearch = seen.count(101) || seen.count(103)
                             || seen.count(202) || seen.count(206);
    ASSERT_TRUE(missedByTheSearch);
  }
  {
    TernaryDomain below8(LsValue::mkZero(w), LsValue(w, 0xff));
    LsValue t(w, 1);
    LsValue s(w, 101 * 103 + 1);
    LsValue cur(w, 5);
    LsChildren ch{&s, &cur};
    ASSERT_FALSE(isInvertible(urem, 1, t, ch, below8));
    std::set<uint64_t> seen;
    for (uint32_t i = 0; i < 20000; ++i)
    {
      std::optional<LsValue> v =
          tryConsistentValue(urem, 1, t, ch, below8, d_rng);
      ASSERT_TRUE(v.has_value());
      seen.insert(v->toInteger().getUnsignedLong());
    }
    ASSERT_TRUE(seen.count(101) || seen.count(103));
  }

  LsRng gen(59);
  for (uint32_t r = 0; r < 500; ++r)
  {
    LsValue fixed = gen.randomValue(w) & gen.randomValue(w);
    LsValue bits = gen.randomValue(w) & fixed;
    TernaryDomain x(bits, bits | ~fixed);
    if (!x.hasFixedBits())
    {
      continue;
    }
    LsValue s = gen.randomValue(w);
    LsValue t = r % 2 == 0 ? LsValue(w, gen.pickIndex(8))
                           : gen.randomValue(w).unsignedRemTotal(inc(s));
    LsValue cur = x.apply(gen.randomValue(w));
    LsChildren ch{&s, &cur};
    uint64_t sv = s.toInteger().getUnsignedLong();
    uint64_t tv = t.toInteger().getUnsignedLong();
    bool exists = false;
    for (uint64_t v = 0; v < (uint64_t(1) << w) && !exists; ++v)
    {
      exists = x.matches(LsValue(w, v)) && (v == 0 ? sv : sv % v) == tv;
    }
    std::stringstream ctx;
    ctx << "x=" << x << " s=" << s << " t=" << t;
    bool ic = isInvertible(urem, 1, t, ch, x);
    ASSERT_TRUE(!ic || exists) << ctx.str() << " (wrong yes)";
    if (ic)
    {
      for (uint32_t i = 0; i < 20; ++i)
      {
        LsValue v = inverseValue(urem, 1, t, ch, x, d_rng);
        uint64_t vv = v.toInteger().getUnsignedLong();
        ASSERT_TRUE(x.matches(v) && (vv == 0 ? sv : sv % vv) == tv)
            << ctx.str() << " inverse=" << v;
      }
    }
  }
}

/**
 * The rules modulo constant bits of x mod s = t (UREM at position 0, goal 9
 * of Step 3) against brute force: every domain with a fixed bit up to 3 bits,
 * sampled at 4 bits. Up to 4 bits there are at most 16 multipliers, so the
 * check is exact here.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_urem_multipliers)
{
  for (uint32_t w = 1; w <= 4; ++w)
  {
    checkRulesDomains({LsKind::UREM}, 0, {w, w}, w == 4);
  }
}

/**
 * x mod s = t at 16 bits, where the solutions s * k + t can be many.
 *
 * With s = 3, t = 1 and x >= 2^15 there are about 11000 solutions: the
 * inverse values are drawn by uniform multipliers, so 300 calls return many
 * different solutions, not only the first one the search finds.
 *
 * With s = 7, t = 3 and the low byte of x fixed to 42, the solutions are
 * sparse (x = 256 a + 42 with a = 6 mod 7): the search jumps from one
 * matching value to the next and finds them.
 *
 * On random domains and targets, the check never says yes wrongly, says yes
 * whenever a solution exists in all but a few cases (the search is bounded),
 * and the inverse values are always solutions that match x.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_urem_multipliers_wide)
{
  const uint32_t w = 16;
  OpInfo urem{LsKind::UREM};
  {
    TernaryDomain x(LsValue(w, 0x8000), LsValue::mkOnes(w));
    LsValue s(w, 3), t(w, 1), cur(w, 0x8000);
    LsChildren ch{&cur, &s};
    ASSERT_TRUE(isInvertible(urem, 0, t, ch, x));
    std::set<uint64_t> seen;
    for (uint32_t i = 0; i < 300; ++i)
    {
      LsValue v = inverseValue(urem, 0, t, ch, x, d_rng);
      uint64_t vv = v.toInteger().getUnsignedLong();
      ASSERT_TRUE(x.matches(v) && vv % 3 == 1) << v;
      seen.insert(vv);
    }
    ASSERT_GT(seen.size(), 250u);
  }
  {
    TernaryDomain x(LsValue(w, 42), LsValue(w, 0xff2a));
    LsValue s(w, 7), t(w, 3), cur(w, 42);
    LsChildren ch{&cur, &s};
    ASSERT_TRUE(isInvertible(urem, 0, t, ch, x));
    for (uint32_t i = 0; i < 100; ++i)
    {
      LsValue v = inverseValue(urem, 0, t, ch, x, d_rng);
      uint64_t vv = v.toInteger().getUnsignedLong();
      ASSERT_TRUE(vv % 256 == 42 && vv % 7 == 3) << v;
    }
  }

  LsRng gen(61);
  uint32_t solvable = 0;
  uint32_t found = 0;
  for (uint32_t r = 0; r < 500; ++r)
  {
    // A quarter, half or three quarters of the bits fixed.
    LsValue fixed = gen.randomValue(w);
    if (r % 3 == 1)
    {
      fixed = fixed & gen.randomValue(w);
    }
    else if (r % 3 == 2)
    {
      fixed = fixed | gen.randomValue(w);
    }
    LsValue bits = gen.randomValue(w) & fixed;
    TernaryDomain x(bits, bits | ~fixed);
    LsValue s =
        r % 2 == 0 ? LsValue(w, 2 + gen.pickIndex(300)) : gen.randomValue(w);
    LsValue t = gen.randomValue(w).unsignedRemTotal(s);
    LsValue cur = x.apply(gen.randomValue(w));
    LsChildren ch{&cur, &s};
    uint64_t sv = s.toInteger().getUnsignedLong();
    uint64_t tv = t.toInteger().getUnsignedLong();
    uint64_t lo = x.lo().toInteger().getUnsignedLong();
    uint64_t hi = x.hi().toInteger().getUnsignedLong();
    bool exists = false;
    for (uint64_t v = 0; v < (uint64_t(1) << w) && !exists; ++v)
    {
      exists = (v & hi) == v && (v | lo) == v && (sv == 0 ? v : v % sv) == tv;
    }
    std::stringstream ctx;
    ctx << "x=" << x << " s=" << s << " t=" << t;
    bool ic = isInvertible(urem, 0, t, ch, x);
    ASSERT_TRUE(!ic || exists) << ctx.str() << " (wrong yes)";
    solvable += exists;
    found += ic;
    if (ic)
    {
      for (uint32_t i = 0; i < 10; ++i)
      {
        LsValue v = inverseValue(urem, 0, t, ch, x, d_rng);
        uint64_t vv = v.toInteger().getUnsignedLong();
        ASSERT_TRUE(x.matches(v) && (sv == 0 ? vv : vv % sv) == tv)
            << ctx.str() << " inverse=" << v;
      }
    }
  }
  RecordProperty("solvable", solvable);
  RecordProperty("found", found);
  ASSERT_GT(solvable, 100u);
  // The bounded search misses at most a few of the solvable cases.
  ASSERT_GE(found + solvable / 50, solvable);
}

/**
 * isEssential modulo constant bits against FMCAD'20 Def. 5 by brute force
 * (goal 10 of Step 3): child i is essential iff no other child j can produce
 * t alone with a value that matches its own domain. A child whose domain is
 * fixed and the disabled branch of an ITE count as not invertible. Every
 * operator up to 3 bits, every tuple of domains, every target and every
 * assignment that matches the domains; and the example of the paper.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_is_essential)
{
  {
    // n_x + n_s with t = 11, n_x = 10 and n_s in x0: n_x is essential since
    // mcb(x0, 11 - 10) is false (FMCAD'20 Sec. IV); n_s is not, since n_x is
    // free and 11 - 00 = 11.
    LsValue nx(2, 0b10), ns(2, 0b00), t(2, 0b11);
    TernaryDomain full = TernaryDomain::full(2);
    TernaryDomain even = TernaryDomain::fromString("x0");
    LsChildren ch{&nx, &ns};
    LsDomains doms{&full, &even};
    OpInfo add{LsKind::ADD};
    ASSERT_TRUE(isEssential(add, 0, t, ch, doms));
    ASSERT_FALSE(isEssential(add, 1, t, ch, doms));
  }
  for (uint32_t w = 1; w <= 3; ++w)
  {
    for (const auto& [op, widths] : allOps(w))
    {
      uint32_t n = widths.size();
      if (n == 1)
      {
        continue;  // trivially essential
      }
      std::vector<std::vector<LsValue>> assignments = allAssignments(widths);
      uint32_t wt = eval(op, assignments[0]).getSize();
      for (const std::vector<TernaryDomain>& ds : allDomainTuples(widths))
      {
        LsDomains doms;
        for (const TernaryDomain& d : ds)
        {
          doms.push_back(&d);
        }
        for (const std::vector<LsValue>& vals : assignments)
        {
          bool matches = true;
          for (uint32_t i = 0; i < n; ++i)
          {
            matches = matches && ds[i].matches(vals[i]);
          }
          if (!matches)
          {
            continue;
          }
          LsChildren ch;
          for (const LsValue& v : vals)
          {
            ch.push_back(&v);
          }
          for (uint32_t tv = 0; tv < (1u << wt); ++tv)
          {
            LsValue t(wt, tv);
            // Which children can produce t alone within their domain.
            std::vector<bool> invertible(n, false);
            for (uint32_t j = 0; j < n; ++j)
            {
              if (ds[j].isFixed()
                  || (op.kind == LsKind::ITE && j > 0
                      && vals[0].isBitSet(0) != (j == 1)))
              {
                continue;
              }
              for (uint32_t yv = 0; yv < (1u << widths[j]); ++yv)
              {
                std::vector<LsValue> valsy = vals;
                valsy[j] = LsValue(widths[j], yv);
                if (ds[j].matches(valsy[j]) && eval(op, valsy) == t)
                {
                  invertible[j] = true;
                  break;
                }
              }
            }
            for (uint32_t i = 0; i < n; ++i)
            {
              bool expected = true;
              for (uint32_t j = 0; j < n; ++j)
              {
                expected = expected && (j == i || !invertible[j]);
              }
              std::stringstream ctx;
              ctx << opToString(op, widths) << " i=" << i << " t=" << t;
              for (uint32_t j = 0; j < n; ++j)
              {
                ctx << " ch" << j << "=" << vals[j] << "/" << ds[j];
              }
              ASSERT_EQ(isEssential(op, i, t, ch, doms), expected) << ctx.str();
            }
          }
        }
      }
    }
  }
}

/**
 * The rules modulo constant bits of every operator at 6 bits, on random cases
 * compared with brute force (goal 10 of Step 3). At 6 bits the bounded
 * searches of UDIV and UREM still see every candidate, so every condition is
 * exact: isInvertible holds iff some value matching x is a solution, and
 * tryConsistentValue returns a value iff some value matching x is
 * consistent. The values are correct, they cover all solutions and all
 * consistent values when there are at most 8, and two generators with the
 * same seed give the same values.
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_6bits)
{
  const uint32_t w = 6;
  LsRng gen(67);
  uint32_t numCases = 0;
  uint32_t numInvertible = 0;
  uint32_t numCoverage = 0;
  std::vector<std::pair<OpInfo, std::vector<uint32_t>>> ops;
  for (const auto& [op, widths] : allOps(w))
  {
    // A third of the extracts is enough; the others are covered up to 4 bits.
    if (op.kind != LsKind::EXTRACT || (op.hi + op.lo) % 3 == 0)
    {
      ops.push_back({op, widths});
    }
  }
  for (const auto& [op, widths] : ops)
  {
    uint32_t n = widths.size();
    for (uint32_t posX = 0; posX < n; ++posX)
    {
      uint32_t wx = widths[posX];
      bool iteBranch = op.kind == LsKind::ITE && posX > 0;
      for (uint32_t r = 0; r < 40; ++r)
      {
        // A domain with some fixed bit; the children with matching or random
        // values; t the value of the operator half of the time.
        LsValue fixed = gen.randomValue(wx);
        if (r % 3 == 1)
        {
          fixed = fixed & gen.randomValue(wx);
        }
        else if (r % 3 == 2)
        {
          fixed = fixed | gen.randomValue(wx);
        }
        if (isZero(fixed))
        {
          fixed = LsValue::mkOne(wx);
        }
        LsValue bits = gen.randomValue(wx) & fixed;
        TernaryDomain x(bits, bits | ~fixed);
        std::vector<LsValue> vals;
        for (uint32_t i = 0; i < n; ++i)
        {
          vals.push_back(i == posX ? x.apply(gen.randomValue(wx))
                                   : gen.randomValue(widths[i]));
        }
        LsValue t = r % 2 == 0 ? eval(op, vals)
                               : gen.randomValue(eval(op, vals).getSize());
        LsChildren ch;
        for (const LsValue& v : vals)
        {
          ch.push_back(&v);
        }
        std::stringstream ctx;
        ctx << opToString(op, widths) << " pos=" << posX << " x=" << x
            << " t=" << t;
        for (uint32_t i = 0; i < n; ++i)
        {
          ctx << " ch" << i << "=" << vals[i];
        }

        // Brute force: the solutions and the consistent values matching x.
        std::set<uint32_t> solutions;
        std::set<uint32_t> consistent;
        for (uint32_t xv = 0; xv < (1u << wx); ++xv)
        {
          LsValue xval(wx, xv);
          if (!x.matches(xval))
          {
            continue;
          }
          std::vector<LsValue> valsx = vals;
          valsx[posX] = xval;
          if (eval(op, valsx) == t)
          {
            solutions.insert(xv);
          }
          if (iteBranch)
          {
            continue;
          }
          // Consistent: some values of the other children give t.
          std::vector<uint32_t> others;
          for (uint32_t i = 0; i < n; ++i)
          {
            if (i != posX)
            {
              others.push_back(i);
            }
          }
          uint32_t combos = 1;
          for (uint32_t i : others)
          {
            combos <<= widths[i];
          }
          for (uint32_t c = 0; c < combos; ++c)
          {
            uint32_t rest = c;
            for (uint32_t i : others)
            {
              valsx[i] = LsValue(widths[i], rest & ((1u << widths[i]) - 1));
              rest >>= widths[i];
            }
            if (eval(op, valsx) == t)
            {
              consistent.insert(xv);
              break;
            }
          }
        }
        if (iteBranch && x.matches(t))
        {
          consistent.insert(t.toInteger().getUnsignedInt());  // plan D11
        }
        bool expectedIc = !solutions.empty();
        if (iteBranch && vals[0].isBitSet(0) != (posX == 1))
        {
          expectedIc = false;  // the disabled branch
        }
        ASSERT_EQ(isInvertible(op, posX, t, ch, x), expectedIc) << ctx.str();
        ++numCases;
        numInvertible += expectedIc;

        LsRng r1(r), r2(r);
        std::set<uint32_t> seenInv;
        std::set<uint32_t> seenCons;
        uint32_t samples =
            solutions.size() <= 8 && consistent.size() <= 8 ? 256 : 16;
        for (uint32_t i = 0; i < samples; ++i)
        {
          if (expectedIc)
          {
            LsValue v = inverseValue(op, posX, t, ch, x, r1);
            ASSERT_EQ(v, inverseValue(op, posX, t, ch, x, r2)) << ctx.str();
            ASSERT_TRUE(solutions.count(v.toInteger().getUnsignedInt()))
                << ctx.str() << " inverse=" << v;
            seenInv.insert(v.toInteger().getUnsignedInt());
          }
          std::optional<LsValue> c = tryConsistentValue(op, posX, t, ch, x, r1);
          ASSERT_EQ(c, tryConsistentValue(op, posX, t, ch, x, r2)) << ctx.str();
          ASSERT_EQ(c.has_value(), !consistent.empty()) << ctx.str();
          if (c)
          {
            ASSERT_TRUE(consistent.count(c->toInteger().getUnsignedInt()))
                << ctx.str() << " consistent=" << *c;
            seenCons.insert(c->toInteger().getUnsignedInt());
          }
        }
        if (samples == 256)
        {
          ++numCoverage;
          if (expectedIc)
          {
            ASSERT_EQ(seenInv, solutions) << ctx.str() << " (inverse coverage)";
          }
          ASSERT_EQ(seenCons, consistent)
              << ctx.str() << " (consistent coverage)";
        }
      }
    }
  }
  RecordProperty("cases", numCases);
  RecordProperty("invertible", numInvertible);
  RecordProperty("coverage", numCoverage);
}

/**
 * The rules modulo constant bits with values of more than 64 bits, which take
 * another code path in LsValue (goal 10 of Step 3), at 65 and 128 bits on
 * random cases. A value returned by inverseValue matches x and produces t. A
 * value returned by tryConsistentValue matches x and is consistent, which is
 * checked with the base invertibility condition of the other child: some
 * value of it gives t (for unary operators: the value gives t). When t is the
 * current value of the operator, the current value of x is a solution, so the
 * exact conditions (all but UREM) must hold and a consistent value must exist
 * (all but the stage-based UDIV at position 0 and the ITE branches).
 */
TEST_F(TestTheoryWhiteBvLsOps, domain_rules_wide_values)
{
  LsRng gen(71);
  uint32_t numCases = 0;
  uint32_t numInvertible = 0;
  uint32_t numConsistent = 0;
  for (uint32_t w : {65u, 128u})
  {
    std::vector<std::pair<OpInfo, std::vector<uint32_t>>> ops;
    ops.push_back({{LsKind::NOT}, {w}});
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
      ops.push_back({{k}, {w, w}});
    }
    ops.push_back({{LsKind::CONCAT}, {w, 3}});
    ops.push_back({{LsKind::EXTRACT, w - 1, 0}, {w}});
    ops.push_back({{LsKind::EXTRACT, w - 2, 60}, {w}});
    ops.push_back({{LsKind::EXTRACT, 70 % w, 3}, {w}});
    ops.push_back({{LsKind::ITE}, {1, w, w}});
    for (const auto& [op, widths] : ops)
    {
      uint32_t n = widths.size();
      for (uint32_t posX = 0; posX < n; ++posX)
      {
        uint32_t wx = widths[posX];
        for (uint32_t r = 0; r < 60; ++r)
        {
          LsValue fixed = gen.randomValue(wx);
          if (r % 3 == 1)
          {
            fixed = fixed & gen.randomValue(wx) & gen.randomValue(wx);
          }
          if (isZero(fixed))
          {
            fixed = LsValue::mkOne(wx);
          }
          LsValue bits = gen.randomValue(wx) & fixed;
          TernaryDomain x(bits, bits | ~fixed);
          std::vector<LsValue> vals;
          for (uint32_t i = 0; i < n; ++i)
          {
            LsValue v = gen.randomValue(widths[i]);
            // Small values make division, remainder and shifts interesting.
            if (r % 4 == 3 && widths[i] > 1)
            {
              v = v.logicalRightShift(widths[i] - 8);
            }
            vals.push_back(i == posX ? x.apply(v) : v);
          }
          bool tIsCurrent = r % 2 == 0;
          LsValue t = tIsCurrent ? eval(op, vals)
                                 : gen.randomValue(eval(op, vals).getSize());
          LsChildren ch;
          for (const LsValue& v : vals)
          {
            ch.push_back(&v);
          }
          std::stringstream ctx;
          ctx << opToString(op, widths) << " pos=" << posX << " x=" << x
              << " t=" << t;

          bool ic = isInvertible(op, posX, t, ch, x);
          ++numCases;
          numInvertible += ic;
          bool iteBranch = op.kind == LsKind::ITE && posX > 0;
          bool enabled = !iteBranch || vals[0].isBitSet(0) == (posX == 1);
          if (tIsCurrent && op.kind != LsKind::UREM && enabled)
          {
            ASSERT_TRUE(ic) << ctx.str() << " (the current value solves)";
          }
          if (ic)
          {
            for (uint32_t i = 0; i < 4; ++i)
            {
              LsValue v = inverseValue(op, posX, t, ch, x, d_rng);
              std::vector<LsValue> valsx = vals;
              valsx[posX] = v;
              ASSERT_TRUE(x.matches(v)) << ctx.str() << " inverse=" << v;
              ASSERT_EQ(eval(op, valsx), t) << ctx.str() << " inverse=" << v;
            }
          }
          std::optional<LsValue> c =
              tryConsistentValue(op, posX, t, ch, x, d_rng);
          if (tIsCurrent && !iteBranch
              && !(op.kind == LsKind::UDIV && posX == 0))
          {
            ASSERT_TRUE(c.has_value()) << ctx.str() << " (x is consistent)";
          }
          if (!c)
          {
            continue;
          }
          ++numConsistent;
          ASSERT_TRUE(x.matches(*c)) << ctx.str() << " consistent=" << *c;
          std::vector<LsValue> valsc = vals;
          valsc[posX] = *c;
          LsChildren chc;
          for (const LsValue& v : valsc)
          {
            chc.push_back(&v);
          }
          if (n == 1)
          {
            ASSERT_EQ(eval(op, valsc), t) << ctx.str() << " consistent=" << *c;
          }
          else if (iteBranch)
          {
            ASSERT_EQ(*c, t) << ctx.str();
          }
          else if (op.kind != LsKind::ITE)
          {
            ASSERT_TRUE(isInvertible(op, 1 - posX, t, chc))
                << ctx.str() << " consistent=" << *c;
          }
        }
      }
    }
  }
  RecordProperty("cases", numCases);
  RecordProperty("invertible", numInvertible);
  RecordProperty("consistent", numConsistent);
  // Both outcomes occur often enough to exercise the values.
  ASSERT_GT(numInvertible, numCases / 3);
  ASSERT_GT(numConsistent, numCases / 2);
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
      if (w == 3 && op.kind == LsKind::ITE)
      {
        continue;  // three children: width 2 is enough
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

        // MUL, UDIV and UREM are only sound; the others are exact.
        bool exact = allFixed;
        switch (op.kind)
        {
          case LsKind::MUL:
          case LsKind::UDIV:
          case LsKind::UREM: break;
          default: exact = true; break;
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
      }
    }
  }
}

/**
 * The known bits of the domains of ADD, MUL, UDIV and UREM, and of shifts by
 * an amount that is not fixed, EQ and ULT (Step 6, plan Sec. 5.2): examples
 * where the bits that the rules should find are found.
 */
TEST_F(TestTheoryWhiteBvLsOps, forward_domain_known_bits)
{
  auto fd = [](LsKind k, const char* a, const char* b) {
    TernaryDomain x = TernaryDomain::fromString(a);
    TernaryDomain y = TernaryDomain::fromString(b);
    return forwardDomain({k}, {&x, &y}).toString();
  };
  // x even plus 1 is odd; low bits 00 plus 01 are 01.
  ASSERT_EQ(fd(LsKind::ADD, "xxx0", "0001"), "xxx1");
  ASSERT_EQ(fd(LsKind::ADD, "xx00", "0001"), "xx01");
  // Known carries: 0x00 + 0x00 has no carry out of bit 0 or into bit 3.
  ASSERT_EQ(fd(LsKind::ADD, "0x00", "0x00"), "xx00");
  // Even times even is a multiple of 4; two and one trailing zeros give
  // three.
  ASSERT_EQ(fd(LsKind::MUL, "xxx0", "xxx0"), "xx00");
  ASSERT_EQ(fd(LsKind::MUL, "xx00", "xxx0"), "x000");
  // Low bits fixed in both: 01 times 11 is 11.
  ASSERT_EQ(fd(LsKind::MUL, "xx01", "xx11"), "xx11");
  // Small operands do not overflow: [0, 3 * 3] has the leading 0 fixed.
  ASSERT_EQ(fd(LsKind::MUL, "00xx", "00xx"), "xxxx");
  ASSERT_EQ(fd(LsKind::MUL, "000x", "00xx"), "00xx");
  // A divisor of at least 4 leaves a quotient of at most 3.
  ASSERT_EQ(fd(LsKind::UDIV, "xxxx", "x1xx"), "00xx");
  // A divisor in {2, 3} leaves a remainder of at most 2.
  ASSERT_EQ(fd(LsKind::UREM, "xxxx", "001x"), "00xx");
  // A divisor fixed to 4 leaves the low two bits of x.
  ASSERT_EQ(fd(LsKind::UREM, "x1x0", "0100"), "00x0");
  // x < y always: x mod y = x.
  ASSERT_EQ(fd(LsKind::UREM, "00x1", "1xxx"), "00x1");
  // Shifting by 2 or 3 clears the low two bits.
  ASSERT_EQ(fd(LsKind::SHL, "xxxx", "001x"), "xx00");
  ASSERT_EQ(fd(LsKind::LSHR, "xxxx", "001x"), "00xx");
  // Disjoint domains are never equal; separated ranges compare fixed.
  ASSERT_EQ(fd(LsKind::EQ, "1xxx", "0xxx"), "0");
  ASSERT_EQ(fd(LsKind::EQ, "1xxx", "xxx0"), "x");
  ASSERT_EQ(fd(LsKind::ULT, "00xx", "1xxx"), "1");
  ASSERT_EQ(fd(LsKind::ULT, "1xxx", "0xxx"), "0");
  ASSERT_EQ(fd(LsKind::ULT, "x0xx", "x1xx"), "x");
}

/**
 * The domains of the operators are sound at larger widths, including the
 * multi-word ones: on random domains (some with few free bits) and random
 * values that match them, the value of the operator matches its domain.
 */
TEST_F(TestTheoryWhiteBvLsOps, forward_domain_wide)
{
  LsRng gen(73);
  for (uint32_t w : {5u, 8u, 16u, 64u, 65u, 128u})
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
      for (uint32_t r = 0; r < 200; ++r)
      {
        std::vector<TernaryDomain> ds;
        for (uint32_t i = 0; i < 2; ++i)
        {
          LsValue fixed = gen.randomValue(w);
          if (r % 3 == 1)
          {
            fixed = fixed | gen.randomValue(w) | gen.randomValue(w);
          }
          else if (r % 3 == 2)
          {
            // Small values: only the low bits free.
            fixed = ~LsValue::mkOnes(w).logicalRightShift(w - (w < 8 ? 2 : 6));
          }
          LsValue bits = gen.randomValue(w) & fixed;
          ds.emplace_back(bits, bits | ~fixed);
        }
        LsDomains doms{&ds[0], &ds[1]};
        TernaryDomain fd = forwardDomain({k}, doms);
        for (uint32_t i = 0; i < 20; ++i)
        {
          LsValue a = ds[0].apply(gen.randomValue(w));
          LsValue b = ds[1].apply(gen.randomValue(w));
          LsValue v = evaluate({k}, {&a, &b});
          ASSERT_TRUE(fd.matches(v))
              << k << " w=" << w << " x=" << ds[0] << " y=" << ds[1]
              << " domain=" << fd << " a=" << a << " b=" << b << " v=" << v;
        }
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
