/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * White box testing of the local search engine (theory/bv/ls/ls_engine.h).
 */

#include <vector>

#include "test.h"
#include "theory/bv/ls/ls_engine.h"

namespace cvc5::internal {

using namespace theory::bv::ls;

namespace test {

class TestTheoryWhiteBvLsEngine : public TestInternal
{
 protected:
  static uint32_t mkConst(LsEngine& e, uint32_t w, uint32_t v)
  {
    return e.mkLeaf(w, LsValue(w, v));
  }

  static uint32_t mkVar(LsEngine& e, uint32_t w)
  {
    return e.mkLeaf(w, std::nullopt);
  }

  /**
   * Build a random DAG over 4-bit and Boolean nodes in e, drawing from rng,
   * and return its roots.
   */
  static std::vector<uint32_t> mkRandomDag(LsEngine& e, LsRng& rng)
  {
    const uint32_t w = 4;
    std::vector<uint32_t> bvs;
    std::vector<uint32_t> bools;
    for (uint32_t i = 0; i < 4; ++i)
    {
      bvs.push_back(mkVar(e, w));
    }
    for (uint32_t i = 0; i < 2; ++i)
    {
      bools.push_back(mkVar(e, 1));
    }
    bvs.push_back(mkConst(e, w, rng.pickIndex(16)));
    auto pick = [&](const std::vector<uint32_t>& v) {
      return v[rng.pickIndex(v.size())];
    };
    for (uint32_t i = 0; i < 30; ++i)
    {
      switch (rng.pickIndex(13))
      {
        case 0: bvs.push_back(e.mkOp(LsKind::NOT, {pick(bvs)})); break;
        case 1:
          bvs.push_back(e.mkOp(LsKind::AND, {pick(bvs), pick(bvs)}));
          break;
        case 2:
          bvs.push_back(e.mkOp(LsKind::ADD, {pick(bvs), pick(bvs)}));
          break;
        case 3:
          bvs.push_back(e.mkOp(LsKind::MUL, {pick(bvs), pick(bvs)}));
          break;
        case 4:
          bvs.push_back(e.mkOp(LsKind::UDIV, {pick(bvs), pick(bvs)}));
          break;
        case 5:
          bvs.push_back(e.mkOp(LsKind::UREM, {pick(bvs), pick(bvs)}));
          break;
        case 6:
          bvs.push_back(e.mkOp(LsKind::SHL, {pick(bvs), pick(bvs)}));
          break;
        case 7:
          bvs.push_back(e.mkOp(LsKind::LSHR, {pick(bvs), pick(bvs)}));
          break;
        case 8:
        {
          uint32_t a = e.mkOp(LsKind::EXTRACT, {pick(bvs)}, 3, 2);
          uint32_t b = e.mkOp(LsKind::EXTRACT, {pick(bvs)}, 1, 0);
          bvs.push_back(e.mkOp(LsKind::CONCAT, {a, b}));
          break;
        }
        case 9:
          bvs.push_back(
              e.mkOp(LsKind::ITE, {pick(bools), pick(bvs), pick(bvs)}));
          break;
        case 10:
          bools.push_back(e.mkOp(LsKind::EQ, {pick(bvs), pick(bvs)}));
          break;
        case 11:
          bools.push_back(e.mkOp(LsKind::ULT, {pick(bvs), pick(bvs)}));
          break;
        default:
          bools.push_back(rng.flipCoin()
                              ? e.mkOp(LsKind::AND, {pick(bools), pick(bools)})
                              : e.mkOp(LsKind::NOT, {pick(bools)}));
          break;
      }
    }
    std::vector<uint32_t> roots;
    for (uint32_t i = 0; i < 3; ++i)
    {
      roots.push_back(pick(bools));
    }
    return roots;
  }
};

TEST_F(TestTheoryWhiteBvLsEngine, hash_consing_and_folding)
{
  LsEngine e(1);
  uint32_t x = mkVar(e, 8);
  uint32_t y = mkVar(e, 8);
  uint32_t c3 = mkConst(e, 8, 3);
  uint32_t c4 = mkConst(e, 8, 4);
  ASSERT_EQ(e.mkOp(LsKind::ADD, {x, y}), e.mkOp(LsKind::ADD, {x, y}));
  ASSERT_NE(e.mkOp(LsKind::ADD, {x, y}), e.mkOp(LsKind::ADD, {y, x}));
  ASSERT_EQ(e.mkOp(LsKind::EXTRACT, {x}, 3, 0),
            e.mkOp(LsKind::EXTRACT, {x}, 3, 0));
  ASSERT_NE(e.mkOp(LsKind::EXTRACT, {x}, 3, 0),
            e.mkOp(LsKind::EXTRACT, {x}, 4, 1));

  uint32_t sum = e.mkOp(LsKind::ADD, {c3, c4});
  ASSERT_TRUE(e.isConst(sum));
  ASSERT_EQ(e.value(sum), LsValue(8, 7u));

  uint32_t t = mkConst(e, 1, 1);
  uint32_t f = mkConst(e, 1, 0);
  ASSERT_EQ(e.mkOp(LsKind::ITE, {t, x, y}), x);
  ASSERT_EQ(e.mkOp(LsKind::ITE, {f, x, y}), y);
}

/** FMSD'17 Example 23: v + v + 2 = 0 needs consistent values. */
TEST_F(TestTheoryWhiteBvLsEngine, example23)
{
  for (uint64_t seed = 0; seed < 20; ++seed)
  {
    LsEngine e(seed);
    e.setCheckInvariants(true);
    uint32_t v = mkVar(e, 4);
    uint32_t sum =
        e.mkOp(LsKind::ADD, {e.mkOp(LsKind::ADD, {v, v}), mkConst(e, 4, 2)});
    uint32_t root = e.mkOp(LsKind::EQ, {sum, mkConst(e, 4, 0)});
    e.setRoots({root});
    ASSERT_EQ(e.solve(10000, 0), LsResult::SAT) << "seed " << seed;
    uint32_t val = e.value(v).getValue().getUnsignedInt();
    ASSERT_TRUE(val == 7 || val == 15) << "seed " << seed << " v=" << val;
    ASSERT_GT(e.stats().propsCons, 0u) << "seed " << seed;
  }
}

/**
 * FMSD'17 Example 23 with the structure of the paper: p1 = v + 2,
 * p2 = v + p1, root p2 = 0, at width 2. The constant forces inverse values at
 * p1, so the search depends on consistent values at p2.
 */
TEST_F(TestTheoryWhiteBvLsEngine, example23_paper)
{
  for (uint64_t seed = 0; seed < 20; ++seed)
  {
    LsEngine e(seed);
    e.setCheckInvariants(true);
    uint32_t v = mkVar(e, 2);
    uint32_t p1 = e.mkOp(LsKind::ADD, {v, mkConst(e, 2, 2)});
    uint32_t p2 = e.mkOp(LsKind::ADD, {v, p1});
    e.setRoots({e.mkOp(LsKind::EQ, {p2, mkConst(e, 2, 0)})});
    ASSERT_EQ(e.solve(10000, 0), LsResult::SAT) << "seed " << seed;
    uint32_t val = e.value(v).getValue().getUnsignedInt();
    ASSERT_TRUE(val == 1 || val == 3) << "seed " << seed << " v=" << val;
    ASSERT_GT(e.stats().propsCons, 0u) << "seed " << seed;
  }
}

/** A propagation that ends at the current value of its leaf is no move. */
TEST_F(TestTheoryWhiteBvLsEngine, noop_moves)
{
  // x <u 0 at width 1: the only consistent value for x is 0, its initial
  // value, so no propagation changes anything.
  LsEngine e(1);
  uint32_t x = mkVar(e, 1);
  e.setRoots({e.mkOp(LsKind::ULT, {x, mkConst(e, 1, 0)})});
  ASSERT_EQ(e.solve(100, 0), LsResult::UNKNOWN);
  ASSERT_GE(e.stats().props, 100u);
  ASSERT_EQ(e.stats().moves, 0u);
  ASSERT_EQ(e.stats().updates, 0u);
}

/** x * 3 = 7 needs the inverse value of MUL. */
TEST_F(TestTheoryWhiteBvLsEngine, mul_odd_constant)
{
  for (uint64_t seed = 0; seed < 20; ++seed)
  {
    LsEngine e(seed);
    e.setCheckInvariants(true);
    uint32_t x = mkVar(e, 8);
    uint32_t prod = e.mkOp(LsKind::MUL, {x, mkConst(e, 8, 3)});
    e.setRoots({e.mkOp(LsKind::EQ, {prod, mkConst(e, 8, 7)})});
    ASSERT_EQ(e.solve(10000, 0), LsResult::SAT) << "seed " << seed;
    ASSERT_EQ((e.value(x) * LsValue(8, 3u)), LsValue(8, 7u));
  }
}

/** x * y = 35 with x, y > 1: a factorization, several roots. */
TEST_F(TestTheoryWhiteBvLsEngine, factorization)
{
  for (uint64_t seed = 0; seed < 10; ++seed)
  {
    LsEngine e(seed);
    uint32_t x = mkVar(e, 8);
    uint32_t y = mkVar(e, 8);
    uint32_t one = mkConst(e, 8, 1);
    e.setRoots(
        {e.mkOp(LsKind::EQ, {e.mkOp(LsKind::MUL, {x, y}), mkConst(e, 8, 35)}),
         e.mkOp(LsKind::ULT, {one, x}),
         e.mkOp(LsKind::ULT, {one, y}),
         e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 36)}),
         e.mkOp(LsKind::ULT, {y, mkConst(e, 8, 36)})});
    ASSERT_EQ(e.solve(0, 0), LsResult::SAT) << "seed " << seed;
    uint32_t xv = e.value(x).getValue().getUnsignedInt();
    uint32_t yv = e.value(y).getValue().getUnsignedInt();
    ASSERT_TRUE((xv == 5 && yv == 7) || (xv == 7 && yv == 5))
        << "seed " << seed << " x=" << xv << " y=" << yv;
  }
}

TEST_F(TestTheoryWhiteBvLsEngine, unknown)
{
  // Unsatisfiable: the propagation budget runs out.
  LsEngine e(1);
  uint32_t x = mkVar(e, 8);
  e.setRoots({e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 0)})});
  ASSERT_EQ(e.solve(1000, 0), LsResult::UNKNOWN);
  ASSERT_GE(e.stats().props, 1000u);
  // Each call gets its own budget.
  ASSERT_EQ(e.solve(1000, 0), LsResult::UNKNOWN);
  ASSERT_GE(e.stats().props, 2000u);
  // The update budget.
  uint64_t updates = e.stats().updates;
  ASSERT_EQ(e.solve(0, 100), LsResult::UNKNOWN);
  ASSERT_GE(e.stats().updates, updates + 100);

  // A constant false root.
  LsEngine e2(1);
  uint32_t f = e2.mkOp(LsKind::EQ, {mkConst(e2, 4, 1), mkConst(e2, 4, 2)});
  ASSERT_TRUE(e2.isConst(f));
  e2.setRoots({f});
  ASSERT_EQ(e2.solve(0, 0), LsResult::UNKNOWN);

  // Termination requested.
  LsEngine e3(1);
  uint32_t y = mkVar(e3, 8);
  e3.setRoots({e3.mkOp(LsKind::EQ, {y, mkConst(e3, 8, 9)})});
  ASSERT_EQ(e3.solve(0, 0, [] { return true; }), LsResult::UNKNOWN);
  ASSERT_EQ(e3.solve(0, 0), LsResult::SAT);

  // No roots.
  LsEngine e4(1);
  ASSERT_EQ(e4.solve(0, 0), LsResult::SAT);
}

/** Leaf values persist when the roots change. */
TEST_F(TestTheoryWhiteBvLsEngine, incremental)
{
  LsEngine e(3);
  e.setCheckInvariants(true);
  uint32_t x = mkVar(e, 8);
  uint32_t y = mkVar(e, 8);
  uint32_t r1 = e.mkOp(LsKind::EQ, {x, mkConst(e, 8, 5)});
  e.setRoots({r1});
  ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
  ASSERT_EQ(e.value(x), LsValue(8, 5u));

  uint32_t r2 =
      e.mkOp(LsKind::EQ, {y, e.mkOp(LsKind::ADD, {x, mkConst(e, 8, 1)})});
  e.setRoots({r1, r2, r1});
  ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
  ASSERT_EQ(e.value(x), LsValue(8, 5u));
  ASSERT_EQ(e.value(y), LsValue(8, 6u));

  // Dropping a root keeps the values.
  e.setRoots({r2});
  ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
  ASSERT_EQ(e.value(y), LsValue(8, 6u));
}

/** The same seed gives the same run. */
TEST_F(TestTheoryWhiteBvLsEngine, deterministic)
{
  for (uint64_t seed = 0; seed < 10; ++seed)
  {
    LsEngine e1(seed);
    LsEngine e2(seed);
    LsRng g1(seed + 100);
    LsRng g2(seed + 100);
    e1.setRoots(mkRandomDag(e1, g1));
    e2.setRoots(mkRandomDag(e2, g2));
    LsResult res1 = e1.solve(2000, 0);
    LsResult res2 = e2.solve(2000, 0);
    ASSERT_EQ(res1, res2);
    ASSERT_EQ(e1.numNodes(), e2.numNodes());
    ASSERT_EQ(e1.stats().moves, e2.stats().moves);
    ASSERT_EQ(e1.stats().props, e2.stats().props);
    ASSERT_EQ(e1.stats().updates, e2.stats().updates);
    for (uint32_t id = 0; id < e1.numNodes(); ++id)
    {
      ASSERT_EQ(e1.value(id), e2.value(id));
    }
  }
}

/** The invariants hold after every move on random DAGs. */
TEST_F(TestTheoryWhiteBvLsEngine, invariants_random)
{
  uint32_t numSat = 0;
  for (uint64_t seed = 0; seed < 100; ++seed)
  {
    LsEngine e(seed);
    e.setCheckInvariants(true);
    LsRng g(seed);
    std::vector<uint32_t> roots = mkRandomDag(e, g);
    e.setRoots(roots);
    if (e.solve(2000, 0) == LsResult::SAT)
    {
      ++numSat;
      for (uint32_t r : roots)
      {
        ASSERT_TRUE(e.value(r).isBitSet(0)) << "seed " << seed;
      }
    }
    ASSERT_TRUE(e.checkInvariants()) << "seed " << seed;
    // Change the roots and continue.
    std::vector<uint32_t> roots2 = mkRandomDag(e, g);
    roots2.push_back(roots[0]);
    e.setRoots(roots2);
    e.solve(500, 0);
    ASSERT_TRUE(e.checkInvariants()) << "seed " << seed;
  }
  // Most random instances are satisfiable and easy.
  ASSERT_GT(numSat, 50u);
}

}  // namespace test
}  // namespace cvc5::internal
