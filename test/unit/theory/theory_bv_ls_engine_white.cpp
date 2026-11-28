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
   * with numConsts 4-bit constants among its leaves, and return its roots.
   */
  static std::vector<uint32_t> mkRandomDag(LsEngine& e,
                                           LsRng& rng,
                                           uint32_t numConsts = 1)
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
    for (uint32_t i = 0; i < numConsts; ++i)
    {
      bvs.push_back(mkConst(e, w, rng.pickIndex(16)));
    }
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
  // SEXT keeps its number of added bits.
  ASSERT_EQ(e.mkOp(LsKind::SEXT, {x}, 2), e.mkOp(LsKind::SEXT, {x}, 2));
  ASSERT_NE(e.mkOp(LsKind::SEXT, {x}, 2), e.mkOp(LsKind::SEXT, {x}, 3));
  ASSERT_EQ(e.value(e.mkOp(LsKind::SEXT, {c4}, 3)), LsValue(11, 4u));

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
    uint32_t val = e.value(v).toInteger().getUnsignedInt();
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
    uint32_t val = e.value(v).toInteger().getUnsignedInt();
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
    uint32_t xv = e.value(x).toInteger().getUnsignedInt();
    uint32_t yv = e.value(y).toInteger().getUnsignedInt();
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

/* -------------------------------------------------------------------------- */
/* Constant bits (prop-c, Step 4)                                             */
/* -------------------------------------------------------------------------- */

/** An engine that uses constant bits. */
static LsConfig constBitsConfig()
{
  LsConfig config;
  config.constBits = true;
  return config;
}

/**
 * With constant bits, operator nodes get the domain computed from their
 * children, and a node whose domain is fixed is a constant (plan D14).
 * Without them, every operator node has the domain without fixed bits.
 */
TEST_F(TestTheoryWhiteBvLsEngine, const_bits_domains)
{
  LsEngine e(1, constBitsConfig());
  uint32_t x = mkVar(e, 4);
  uint32_t masked = e.mkOp(LsKind::AND, {mkConst(e, 4, 0b1110), x});
  ASSERT_EQ(e.domain(x).toString(), "xxxx");
  ASSERT_EQ(e.domain(masked).toString(), "xxx0");
  uint32_t low = e.mkOp(LsKind::EXTRACT, {x}, 1, 0);
  uint32_t cat = e.mkOp(LsKind::CONCAT, {low, mkConst(e, 2, 0b01)});
  ASSERT_EQ(e.domain(cat).toString(), "xx01");
  ASSERT_EQ(e.numFixedOps(), 0u);
  // x & 0 is 0 for every x: a constant.
  uint32_t zero = e.mkOp(LsKind::AND, {x, mkConst(e, 4, 0)});
  ASSERT_TRUE(e.isConst(zero));
  ASSERT_EQ(e.value(zero), LsValue(4, 0u));
  ASSERT_EQ(e.numFixedOps(), 1u);

  LsEngine base(1);
  uint32_t bx = mkVar(base, 4);
  uint32_t bzero = base.mkOp(LsKind::AND, {bx, mkConst(base, 4, 0)});
  ASSERT_FALSE(base.isConst(bzero));
  ASSERT_EQ(base.domain(bzero).toString(), "xxxx");
}

/**
 * A root whose domain is fixed to false is a constant, so solve stops at once
 * with UNKNOWN (and bit-blasting answers); the base local search searches
 * until its budget runs out.
 */
TEST_F(TestTheoryWhiteBvLsEngine, const_bits_false_root)
{
  for (bool constBits : {false, true})
  {
    LsConfig config;
    config.constBits = constBits;
    LsEngine e(1, config);
    uint32_t x = mkVar(e, 4);
    uint32_t masked = e.mkOp(LsKind::AND, {x, mkConst(e, 4, 0b0011)});
    // Bit 2 of x & 0011 is 0 for every x. (That (x & 0011) = 0100 is false
    // too needs the domains of EQ from Step 6.)
    uint32_t root = e.mkOp(LsKind::EXTRACT, {masked}, 2, 2);
    ASSERT_EQ(e.isConst(root), constBits);
    e.setRoots({root});
    ASSERT_EQ(e.solve(500, 0), LsResult::UNKNOWN);
    ASSERT_EQ(e.stats().props == 0, constBits);
  }
}

/**
 * FMCAD'20 Sec. IV: with x even (domain x0), x * s = 01 has neither an
 * inverse nor a consistent value for x. Since Step 6 the domains alone show
 * it: the product is even, so the root is the constant false and solve stops
 * at once.
 *
 * A conflict during the search (Fig. 2, lines 5-6): in ite(c, b, a) = 11 with
 * a in 0x and b in 1x, while c selects a, propagating 11 to the branch a has
 * no consistent value (plan D11). The formula is satisfiable (c true, b =
 * 11); the search records conflicts at the ITE and finds a model.
 */
TEST_F(TestTheoryWhiteBvLsEngine, const_bits_conflict)
{
  {
    LsEngine e(1, constBitsConfig());
    uint32_t even = e.mkOp(LsKind::CONCAT, {mkVar(e, 1), mkConst(e, 1, 0)});
    ASSERT_EQ(e.domain(even).toString(), "x0");
    uint32_t mul = e.mkOp(LsKind::MUL, {even, mkVar(e, 2)});
    ASSERT_EQ(e.domain(mul).toString(), "x0");
    uint32_t root = e.mkOp(LsKind::EQ, {mul, mkConst(e, 2, 0b01)});
    ASSERT_TRUE(e.isConst(root));
    e.setRoots({root});
    ASSERT_EQ(e.solve(1000, 0), LsResult::UNKNOWN);
    ASSERT_EQ(e.stats().props, 0u);
  }
  uint64_t conflicts = 0;
  for (uint64_t seed = 0; seed < 20; ++seed)
  {
    LsEngine e(seed, constBitsConfig());
    e.setCheckInvariants(true);
    uint32_t a = e.mkOp(LsKind::CONCAT, {mkConst(e, 1, 0), mkVar(e, 1)});
    uint32_t b = e.mkOp(LsKind::CONCAT, {mkConst(e, 1, 1), mkVar(e, 1)});
    uint32_t c = mkVar(e, 1);
    uint32_t ite = e.mkOp(LsKind::ITE, {c, b, a});
    uint32_t root = e.mkOp(LsKind::EQ, {ite, mkConst(e, 2, 0b11)});
    e.setRoots({root});
    ASSERT_EQ(e.solve(1000, 0), LsResult::SAT) << "seed " << seed;
    ASSERT_TRUE(e.value(root).isBitSet(0));
    conflicts += e.stats().conflictsByKind[static_cast<uint32_t>(LsKind::ITE)];
  }
  ASSERT_GT(conflicts, 0u);
}

/**
 * currentValue: the moves keep only the leaves and the nodes reachable from
 * the roots up to date; any other node is evaluated from the leaves. (The
 * adapter reads model values this way: the node of a purification skolem
 * need not be reachable.)
 */
TEST_F(TestTheoryWhiteBvLsEngine, current_value)
{
  for (bool constBits : {false, true})
  {
    LsConfig config;
    config.constBits = constBits;
    LsEngine e(1, config);
    uint32_t x = mkVar(e, 4);
    uint32_t y = mkVar(e, 4);
    uint32_t sum = e.mkOp(LsKind::ADD, {x, y});     // not reachable
    uint32_t prod = e.mkOp(LsKind::MUL, {sum, x});  // not reachable
    e.setRoots({e.mkOp(LsKind::EQ, {x, mkConst(e, 4, 5)})});
    ASSERT_EQ(e.solve(100, 0), LsResult::SAT);
    ASSERT_EQ(e.value(x), LsValue(4, 5u));
    LsValue expected = (e.value(x) + e.value(y)) * e.value(x);
    ASSERT_EQ(e.currentValue(prod), expected);
    ASSERT_EQ(e.currentValue(sum), e.value(x) + e.value(y));
    ASSERT_EQ(e.currentValue(x), LsValue(4, 5u));
  }
}

/**
 * Without constants every domain is the one without fixed bits, so with or
 * without constant bits the rules are the base rules and the runs are the
 * same, draw for draw.
 */
TEST_F(TestTheoryWhiteBvLsEngine, const_bits_full_domains_same_run)
{
  for (uint64_t seed = 0; seed < 30; ++seed)
  {
    LsEngine e1(seed);
    LsEngine e2(seed, constBitsConfig());
    LsRng g1(seed + 200);
    LsRng g2(seed + 200);
    e1.setRoots(mkRandomDag(e1, g1, 0));
    e2.setRoots(mkRandomDag(e2, g2, 0));
    ASSERT_EQ(e2.domainStats().bitsFixed, 0u);
    LsResult res1 = e1.solve(2000, 0);
    LsResult res2 = e2.solve(2000, 0);
    ASSERT_EQ(res1, res2) << "seed " << seed;
    ASSERT_EQ(e1.stats().moves, e2.stats().moves) << "seed " << seed;
    ASSERT_EQ(e1.stats().props, e2.stats().props) << "seed " << seed;
    ASSERT_EQ(e1.stats().propsInv, e2.stats().propsInv) << "seed " << seed;
    ASSERT_EQ(e1.stats().conflicts, e2.stats().conflicts) << "seed " << seed;
    for (uint32_t id = 0; id < e1.numNodes(); ++id)
    {
      ASSERT_EQ(e1.value(id), e2.value(id)) << "seed " << seed;
    }
  }
}

/**
 * With constant bits on random DAGs with several constants: the invariants,
 * which include that every value matches its domain, hold after every move;
 * a SAT answer makes every root true; the same seed gives the same run; and
 * the DAGs do have constant bits.
 */
TEST_F(TestTheoryWhiteBvLsEngine, const_bits_random)
{
  uint32_t numSat = 0;
  uint64_t bitsFixed = 0;
  // The base local search on the same DAGs, for comparison only.
  uint32_t numSatBase = 0;
  uint64_t props = 0;
  uint64_t propsBase = 0;
  for (uint64_t seed = 0; seed < 100; ++seed)
  {
    LsEngine base(seed);
    LsRng gBase(seed);
    base.setRoots(mkRandomDag(base, gBase, 4));
    numSatBase += base.solve(2000, 0) == LsResult::SAT;
    propsBase += base.stats().props;

    LsEngine e(seed, constBitsConfig());
    LsEngine same(seed, constBitsConfig());
    e.setCheckInvariants(true);
    LsRng g(seed);
    LsRng gSame(seed);
    std::vector<uint32_t> roots = mkRandomDag(e, g, 4);
    same.setRoots(mkRandomDag(same, gSame, 4));
    e.setRoots(roots);
    LsResult res = e.solve(2000, 0);
    ASSERT_EQ(res, same.solve(2000, 0)) << "seed " << seed;
    ASSERT_EQ(e.stats().props, same.stats().props) << "seed " << seed;
    bitsFixed += e.domainStats().bitsFixed;
    props += e.stats().props;
    if (res == LsResult::SAT)
    {
      ++numSat;
      for (uint32_t r : roots)
      {
        ASSERT_TRUE(e.value(r).isBitSet(0)) << "seed " << seed;
      }
    }
    ASSERT_TRUE(e.checkInvariants()) << "seed " << seed;
    // Change the roots and continue, as an incremental check-sat does.
    std::vector<uint32_t> roots2 = mkRandomDag(e, g, 4);
    roots2.push_back(roots[0]);
    e.setRoots(roots2);
    e.solve(500, 0);
    ASSERT_TRUE(e.checkInvariants()) << "seed " << seed;
  }
  RecordProperty("sat", numSat);
  RecordProperty("satBase", numSatBase);
  RecordProperty("props", static_cast<int64_t>(props));
  RecordProperty("propsBase", static_cast<int64_t>(propsBase));
  RecordProperty("bitsFixed", static_cast<int64_t>(bitsFixed));
  ASSERT_GT(numSat, 40u);
  // The domains of Step 4 come from the structure (masks, shifts by
  // constants, concat, extract, ITE); Step 6 adds arithmetic and predicates.
  ASSERT_GT(bitsFixed, 20u);
}

/**
 * prop-cb+ (Step 2): the asserted inequalities are the ULT roots (positive)
 * and the ULT children of NOT roots (negative), and only with ineqBounds.
 */
TEST_F(TestTheoryWhiteBvLsEngine, ineq_roots)
{
  for (bool on : {false, true})
  {
    LsConfig config;
    config.constBits = true;
    config.ineqBounds = on;
    LsEngine e(1, config);
    uint32_t x = mkVar(e, 8);
    uint32_t y = mkVar(e, 8);
    uint32_t lt100 = e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 100)});
    uint32_t lt50 = e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 50)});
    uint32_t ltxy = e.mkOp(LsKind::ULT, {x, y});
    uint32_t eq = e.mkOp(LsKind::EQ, {x, y});
    // ltxy is only below an AND, which is not an asserted inequality.
    uint32_t conj = e.mkOp(LsKind::AND, {ltxy, eq});
    e.setRoots({lt100, e.mkOp(LsKind::NOT, {lt50}), conj});
    e.solve(1, 0);
    ASSERT_EQ(e.isIneqRoot(lt100, true), on);
    ASSERT_FALSE(e.isIneqRoot(lt100, false));
    ASSERT_EQ(e.isIneqRoot(lt50, false), on);
    ASSERT_FALSE(e.isIneqRoot(lt50, true));
    ASSERT_FALSE(e.isIneqRoot(ltxy, true));
    ASSERT_FALSE(e.isIneqRoot(ltxy, false));
    ASSERT_FALSE(e.isIneqRoot(eq, true));
    ASSERT_FALSE(e.isIneqRoot(conj, true));
  }
}

/**
 * prop-cb+ (Step 3): the bounds of a node are the intersection of the
 * solutions of the asserted inequalities on it that hold with their
 * polarity; other parents give none.
 */
TEST_F(TestTheoryWhiteBvLsEngine, ineq_bounds)
{
  LsConfig config;
  config.constBits = true;
  config.ineqBounds = true;
  LsEngine e(1, config);
  uint32_t x = mkVar(e, 8);
  uint32_t a = mkVar(e, 8);
  uint32_t c110 = mkConst(e, 8, 110);
  uint32_t c101 = mkConst(e, 8, 101);
  // x = 110 and a = 101.
  e.setRoots({e.mkOp(LsKind::EQ, {x, c110}), e.mkOp(LsKind::EQ, {a, c101})});
  ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
  ASSERT_EQ(e.value(x), LsValue(8, 110));
  ASSERT_EQ(e.value(a), LsValue(8, 101));
  // a <u x gives x in [102, 255] and a in [0, 109]; x <u 120, [0, 119];
  // not (x <u 105), [105, 255]; x = 110 is no inequality.
  uint32_t ax = e.mkOp(LsKind::ULT, {a, x});
  uint32_t x120 = e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 120)});
  uint32_t x105 = e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 105)});
  e.setRoots(
      {ax, x120, e.mkOp(LsKind::NOT, {x105}), e.mkOp(LsKind::EQ, {x, c110})});
  ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
  std::optional<LsBounds> bx = e.ineqBounds(x, LsKind::ULT);
  ASSERT_TRUE(bx);
  ASSERT_EQ(bx->lo, LsValue(8, 105));
  ASSERT_EQ(bx->hi, LsValue(8, 119));
  std::optional<LsBounds> ba = e.ineqBounds(a, LsKind::ULT);
  ASSERT_TRUE(ba);
  ASSERT_EQ(ba->lo, LsValue(8, 0));
  ASSERT_EQ(ba->hi, LsValue(8, 109));
  // Without ineqBounds there are no bounds.
  LsEngine e2(1);
  uint32_t y = mkVar(e2, 8);
  e2.setRoots({e2.mkOp(LsKind::ULT, {y, mkConst(e2, 8, 5)})});
  ASSERT_EQ(e2.solve(0, 0), LsResult::SAT);
  ASSERT_FALSE(e2.ineqBounds(y, LsKind::ULT));
}

/**
 * prop-cb+ (Step 5): the example of FMCAD'20 Sec. V-A. With x = 110 and
 * a = 101, a <u x gives x the bounds [102, 255], which leave no inverse
 * value for x <u 100: the step falls back to a consistent value. With a =
 * 50 the bounds are [51, 255], and the inverse value lies in [51, 99].
 */
TEST_F(TestTheoryWhiteBvLsEngine, ineq_bounds_moves)
{
  for (uint32_t a0 : {101u, 50u})
  {
    for (uint64_t seed = 1; seed <= 20; ++seed)
    {
      LsConfig config;
      config.probInverse = 1000;
      config.probEssential = 1000;
      config.constBits = true;
      config.ineqBounds = true;
      LsEngine e(seed, config);
      uint32_t x = mkVar(e, 8);
      uint32_t a = mkVar(e, 8);
      e.setRoots({e.mkOp(LsKind::EQ, {x, mkConst(e, 8, 110)}),
                  e.mkOp(LsKind::EQ, {a, mkConst(e, 8, a0)})});
      ASSERT_EQ(e.solve(0, 0), LsResult::SAT);
      LsStats before = e.stats();
      e.setRoots({e.mkOp(LsKind::ULT, {x, mkConst(e, 8, 100)}),
                  e.mkOp(LsKind::ULT, {a, x})});
      e.solve(1, 0);
      const LsStats& after = e.stats();
      ASSERT_EQ(after.propsWithBounds - before.propsWithBounds, 1u);
      if (a0 == 101)
      {
        ASSERT_EQ(after.boundsFallback - before.boundsFallback, 1u);
        ASSERT_EQ(after.propsBounded, before.propsBounded);
      }
      else
      {
        ASSERT_EQ(after.propsBounded - before.propsBounded, 1u);
        ASSERT_EQ(after.boundsFallback, before.boundsFallback);
        ASSERT_FALSE(e.value(x).unsignedLessThan(LsValue(8, 51)));
        ASSERT_TRUE(e.value(x).unsignedLessThan(LsValue(8, 100)));
      }
    }
  }
}

/**
 * prop-cb+ (Step 5): on random DAGs, ineqBounds keeps the invariants, and a
 * run in which no step found bounds is the run of prop-c.
 */
TEST_F(TestTheoryWhiteBvLsEngine, ineq_bounds_random)
{
  uint32_t withBounds = 0;
  uint32_t without = 0;
  for (uint64_t seed = 1; seed <= 300; ++seed)
  {
    LsConfig c1;
    c1.constBits = true;
    LsConfig c2 = c1;
    c2.ineqBounds = true;
    LsEngine e1(seed, c1);
    LsEngine e2(seed, c2);
    LsRng r1(seed);
    LsRng r2(seed);
    e1.setRoots(mkRandomDag(e1, r1, 2));
    e2.setRoots(mkRandomDag(e2, r2, 2));
    e2.setCheckInvariants(true);
    LsResult res1 = e1.solve(2000, 0);
    LsResult res2 = e2.solve(2000, 0);
    ASSERT_TRUE(e2.checkInvariants());
    if (e2.stats().propsWithBounds == 0)
    {
      ++without;
      ASSERT_EQ(res1, res2) << "seed " << seed;
      ASSERT_EQ(e1.stats().moves, e2.stats().moves) << "seed " << seed;
      ASSERT_EQ(e1.stats().props, e2.stats().props) << "seed " << seed;
      ASSERT_EQ(e1.stats().updates, e2.stats().updates) << "seed " << seed;
    }
    else
    {
      ++withBounds;
    }
  }
  ASSERT_GT(withBounds, 0u);
  ASSERT_GT(without, 0u);
}

}  // namespace test
}  // namespace cvc5::internal
