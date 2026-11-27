/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * White box testing of the local search adapter
 * (theory/bv/ls/bv_ls_solver.h).
 */

#include <random>
#include <vector>

#include "expr/skolem_manager.h"
#include "options/bv_options.h"
#include "smt/solver_engine.h"
#include "test_smt.h"
#include "theory/bv/ls/bv_ls_solver.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::bv;
using namespace theory::bv::ls;

namespace test {

class TestTheoryWhiteBvLsSolver : public TestSmt
{
 protected:
  Env& env() { return d_slvEngine->getEnv(); }

  Node mkBv(uint32_t w)
  {
    std::uniform_int_distribution<uint32_t> dist(0, 3);
    Integer v;
    switch (dist(d_gen))
    {
      // Bias towards the special values 0, 1 and ones.
      case 0: v = Integer(d_gen() % 2); break;
      case 1: v = Integer(2).pow(w) - 1; break;
      default:
      {
        for (uint32_t i = 0; i < w; i += 32)
        {
          v = v.multiplyByPow2(32) + Integer(static_cast<uint32_t>(d_gen()));
        }
        v = v.extractBitRange(w, 0);
      }
    }
    return d_nodeManager->mkConst(BitVector(w, v));
  }

  Node mkBool() { return d_nodeManager->mkConst<bool>(d_gen() % 2); }

  Node mkOp(Kind k, const std::vector<Node>& ch)
  {
    return d_nodeManager->mkNode(k, ch);
  }

  /**
   * Translate term (with constant leaves only) and check that the engine
   * folds it to the value of rewrite(term).
   */
  void checkTerm(BvLsSolver& ls, const Node& term)
  {
    std::optional<uint32_t> id = ls.translate(term);
    ASSERT_TRUE(id.has_value()) << term;
    ASSERT_TRUE(ls.d_engine.isConst(*id)) << term;
    const LsValue& v = ls.d_engine.value(*id);
    Node expected = rewrite(term);
    ASSERT_TRUE(expected.isConst()) << term;
    if (term.getType().isBoolean())
    {
      ASSERT_EQ(v.getSize(), 1u) << term;
      ASSERT_EQ(v.isBitSet(0), expected.getConst<bool>()) << term;
    }
    else
    {
      ASSERT_EQ(v.toBitVector(), expected.getConst<BitVector>()) << term;
    }
  }

  Node rewrite(const Node& n) { return env().getRewriter()->rewrite(n); }

  std::mt19937 d_gen{42};
};

/**
 * Every kind the adapter maps: the LS evaluation of the translation equals
 * rewrite of the original term, on random constants.
 */
TEST_F(TestTheoryWhiteBvLsSolver, translation_matches_rewrite)
{
  BvLsSolver ls(env());
  NodeManager* nm = d_nodeManager.get();
  for (uint32_t w : {1u, 2u, 3u, 4u, 7u, 8u, 32u, 33u, 64u, 65u})
  {
    for (uint32_t i = 0; i < 30; ++i)
    {
      Node a = mkBv(w), b = mkBv(w), c = mkBv(w);
      Node p = mkBool(), q = mkBool(), r = mkBool();
      std::vector<Node> terms = {
          // Boolean structure.
          mkOp(Kind::NOT, {p}),
          mkOp(Kind::AND, {p, q, r}),
          mkOp(Kind::OR, {p, q, r}),
          mkOp(Kind::IMPLIES, {p, q}),
          mkOp(Kind::XOR, {p, q}),
          mkOp(Kind::EQUAL, {p, q}),
          mkOp(Kind::ITE, {p, q, r}),
          // Bitwise.
          mkOp(Kind::BITVECTOR_NOT, {a}),
          mkOp(Kind::BITVECTOR_AND, {a, b, c}),
          mkOp(Kind::BITVECTOR_OR, {a, b, c}),
          mkOp(Kind::BITVECTOR_XOR, {a, b, c}),
          mkOp(Kind::BITVECTOR_XNOR, {a, b}),
          mkOp(Kind::BITVECTOR_NAND, {a, b}),
          mkOp(Kind::BITVECTOR_NOR, {a, b}),
          // Predicates.
          mkOp(Kind::EQUAL, {a, b}),
          mkOp(Kind::EQUAL, {a, a}),
          mkOp(Kind::BITVECTOR_COMP, {a, b}),
          mkOp(Kind::BITVECTOR_ULT, {a, b}),
          mkOp(Kind::BITVECTOR_ULE, {a, b}),
          mkOp(Kind::BITVECTOR_UGT, {a, b}),
          mkOp(Kind::BITVECTOR_UGE, {a, b}),
          mkOp(Kind::BITVECTOR_ULTBV, {a, b}),
          mkOp(Kind::BITVECTOR_SLT, {a, b}),
          mkOp(Kind::BITVECTOR_SLE, {a, b}),
          mkOp(Kind::BITVECTOR_SGT, {a, b}),
          mkOp(Kind::BITVECTOR_SGE, {a, b}),
          mkOp(Kind::BITVECTOR_SLTBV, {a, b}),
          // Arithmetic and shifts.
          mkOp(Kind::BITVECTOR_ADD, {a, b, c}),
          mkOp(Kind::BITVECTOR_MULT, {a, b, c}),
          mkOp(Kind::BITVECTOR_NEG, {a}),
          mkOp(Kind::BITVECTOR_SUB, {a, b}),
          mkOp(Kind::BITVECTOR_UDIV, {a, b}),
          mkOp(Kind::BITVECTOR_UREM, {a, b}),
          mkOp(Kind::BITVECTOR_SHL, {a, b}),
          mkOp(Kind::BITVECTOR_LSHR, {a, b}),
          mkOp(Kind::BITVECTOR_ASHR, {a, b}),
          // Conditionals.
          mkOp(Kind::ITE, {p, a, b}),
          mkOp(Kind::BITVECTOR_ITE, {mkBv(1), a, b}),
          // Structural.
          mkOp(Kind::BITVECTOR_CONCAT, {a, mkBv(3), b}),
          utils::mkExtract(a, w - 1, w / 2),
          utils::mkBit(a, w / 3),
          utils::mkSignExtend(a, 5),
          mkOp(Kind::BITVECTOR_ZERO_EXTEND,
               {nm->mkConst(BitVectorZeroExtend(4)), a}),
          utils::mkRepeat(a, 3),
          mkOp(Kind::BITVECTOR_ROTATE_LEFT,
               {nm->mkConst(BitVectorRotateLeft(i % (w + 2))), a}),
          mkOp(Kind::BITVECTOR_ROTATE_RIGHT,
               {nm->mkConst(BitVectorRotateRight(i % (w + 2))), a}),
          mkOp(Kind::BITVECTOR_REDOR, {a}),
          mkOp(Kind::BITVECTOR_REDAND, {a}),
      };
      for (const Node& t : terms)
      {
        ASSERT_NO_FATAL_FAILURE(checkTerm(ls, t));
      }
    }
  }
}

/** Unsupported kinds make check return UNKNOWN. */
TEST_F(TestTheoryWhiteBvLsSolver, unsupported)
{
  BvLsSolver ls(env());
  Node x = d_nodeManager->mkVar("x", d_nodeManager->mkBitVectorType(8));
  Node y = d_nodeManager->mkVar("y", d_nodeManager->mkBitVectorType(8));
  Node fact = mkOp(Kind::EQUAL, {mkOp(Kind::BITVECTOR_SDIV, {x, y}), x});
  ASSERT_EQ(ls.check({fact}), prop::SAT_VALUE_UNKNOWN);
}

/** End to end: facts with variables, model values, roots split. */
TEST_F(TestTheoryWhiteBvLsSolver, check_and_model)
{
  BvLsSolver ls(env());
  NodeManager* nm = d_nodeManager.get();
  TypeNode bv8 = nm->mkBitVectorType(8);
  Node x = nm->mkVar("x", bv8);
  Node y = nm->mkVar("y", bv8);
  Node p = nm->mkVar("p", nm->booleanType());
  Node three = nm->mkConst(BitVector(8, 3u));
  Node seven = nm->mkConst(BitVector(8, 7u));
  // x * 3 = 7, y = x + 1 (as one conjunction), p or x <u y.
  Node f1 = mkOp(Kind::EQUAL, {mkOp(Kind::BITVECTOR_MULT, {x, three}), seven});
  Node f2 = mkOp(
      Kind::AND,
      {mkOp(Kind::EQUAL,
            {y, mkOp(Kind::BITVECTOR_ADD, {x, nm->mkConst(BitVector(8, 1u))})}),
       mkOp(Kind::OR, {p, mkOp(Kind::BITVECTOR_ULT, {x, y})})});
  Node eager = mkOp(Kind::BITVECTOR_EAGER_ATOM, {f2});
  ASSERT_EQ(ls.check({f1, eager}), prop::SAT_VALUE_TRUE);
  BitVector xv = ls.getValue(x).getConst<BitVector>();
  BitVector yv = ls.getValue(y).getConst<BitVector>();
  ASSERT_EQ(xv * BitVector(8, 3u), BitVector(8, 7u));
  ASSERT_EQ(yv, xv + BitVector(8, 1u));
  ASSERT_TRUE(ls.getValue(p).isConst());
  ASSERT_EQ(ls.getLeaves().size(), 3u);
  // Terms that are not leaves have no value.
  ASSERT_TRUE(ls.getValue(f1).isNull());

  // Incremental: a second check with an extra fact keeps the translation.
  Node f3 = mkOp(Kind::NOT, {p});
  ASSERT_EQ(ls.check({f1, eager, f3}), prop::SAT_VALUE_TRUE);
  ASSERT_FALSE(ls.getValue(p).getConst<bool>());
  ASSERT_EQ(ls.getLeaves().size(), 3u);

  // A constant false fact.
  ASSERT_EQ(ls.check({f1, nm->mkConst(false)}), prop::SAT_VALUE_UNKNOWN);
}

/**
 * A purification skolem is translated as the term it purifies, and its
 * definition is not a root.
 */
TEST_F(TestTheoryWhiteBvLsSolver, unpurify)
{
  BvLsSolver ls(env());
  NodeManager* nm = d_nodeManager.get();
  Node x = nm->mkVar("x", nm->mkBitVectorType(8));
  Node b0 = nm->mkConst(BitVector(1, 0u));
  Node b1 = nm->mkConst(BitVector(1, 1u));
  Node cond = mkOp(Kind::EQUAL, {x, nm->mkConst(BitVector(8, 0u))});
  Node t = mkOp(Kind::ITE, {cond, b1, b0});
  Node k = SkolemManager::mkPurifySkolem(t);
  // As term-formula removal leaves it: k = #b1, and k's definition.
  Node f = mkOp(Kind::EQUAL, {b1, k});
  Node def =
      mkOp(Kind::ITE,
           {cond, mkOp(Kind::EQUAL, {k, b1}), mkOp(Kind::EQUAL, {k, b0})});
  ASSERT_TRUE(ls.isPurifyDefinition(def));
  // Not a definition: the branches are swapped.
  Node swapped =
      mkOp(Kind::ITE,
           {cond, mkOp(Kind::EQUAL, {k, b0}), mkOp(Kind::EQUAL, {k, b1})});
  ASSERT_FALSE(ls.isPurifyDefinition(swapped));

  ASSERT_EQ(ls.check({f, def}), prop::SAT_VALUE_TRUE);
  ASSERT_EQ(ls.d_nodeMap.at(k), ls.d_nodeMap.at(t));
  ASSERT_EQ(ls.getValue(x), nm->mkConst(BitVector(8, 0u)));
  ASSERT_EQ(ls.getValue(k), b1);
  ASSERT_EQ(ls.getLeaves().size(), 2u);  // k and x
}

/** The adapter with --bv-ls-const-bits (prop-c, Step 5). */
class TestTheoryWhiteBvLsSolverConstBits : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("bv-ls-const-bits", "true");
    d_slvEngine->finishInit();
  }
};

/**
 * With constant bits, x = a o 0001 has the domain xxxx0001; x * 3 = 147 has
 * the solution x = 49 = 0011 0001, so a = 3. The search finds it, the model
 * is right, and a constant false fact gives UNKNOWN.
 */
TEST_F(TestTheoryWhiteBvLsSolverConstBits, check_and_model)
{
  ASSERT_TRUE(d_slvEngine->getOptions().bv.bvLsConstBits);
  BvLsSolver ls(d_slvEngine->getEnv());
  NodeManager* nm = d_nodeManager.get();
  Node a = nm->mkVar("a", nm->mkBitVectorType(4));
  Node x = nm->mkNode(Kind::BITVECTOR_CONCAT, a, nm->mkConst(BitVector(4, 1u)));
  Node f = nm->mkNode(
      Kind::EQUAL,
      nm->mkNode(Kind::BITVECTOR_MULT, x, nm->mkConst(BitVector(8, 3u))),
      nm->mkConst(BitVector(8, 147u)));
  ASSERT_EQ(ls.check({f}), prop::SAT_VALUE_TRUE);
  ASSERT_EQ(ls.getValue(a).getConst<BitVector>(), BitVector(4, 3u));
  ASSERT_EQ(ls.check({f, nm->mkConst(false)}), prop::SAT_VALUE_UNKNOWN);
}

/**
 * The statistics of constant bits (plan Step 7). In a * 0001 ... the nodes
 * reachable from the root of x * 3 = 147 are a (4 free bits), x = a o 0001
 * (domain xxxx0001), x * 3 (xxxx0011: the low bits of the operands are
 * fixed) and the equality (free): 8 of 21 bits fixed, in 2 nodes. The fact
 * (x & 0) = 0 folds to the constant true (the AND is fixed 0, then the EQ is
 * fixed 1). The AND counts as a node that became a constant by its domain;
 * the EQ of two constants is folded as in ls-base and does not count. The
 * fact is no root.
 * The conflicts by kind add up to the conflicts.
 */
TEST_F(TestTheoryWhiteBvLsSolverConstBits, statistics)
{
  BvLsSolver ls(d_slvEngine->getEnv());
  StatisticsRegistry& reg = d_slvEngine->getEnv().getStatisticsRegistry();
  auto stat = [&reg](const char* name) {
    return reg.registerInt(std::string("theory::bv::ls::") + name).get();
  };
  NodeManager* nm = d_nodeManager.get();
  Node a = nm->mkVar("a", nm->mkBitVectorType(4));
  Node x = nm->mkNode(Kind::BITVECTOR_CONCAT, a, nm->mkConst(BitVector(4, 1u)));
  Node f = nm->mkNode(
      Kind::EQUAL,
      nm->mkNode(Kind::BITVECTOR_MULT, x, nm->mkConst(BitVector(8, 3u))),
      nm->mkConst(BitVector(8, 147u)));
  Node zero = nm->mkConst(BitVector(8, 0u));
  Node g =
      nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_AND, x, zero), zero);
  ASSERT_EQ(ls.check({f, g}), prop::SAT_VALUE_TRUE);
  ASSERT_EQ(stat("numRoots"), 1);
  ASSERT_EQ(stat("numBitsFixed"), 8);
  ASSERT_EQ(stat("numBitsTotal"), 21);
  ASSERT_EQ(stat("numNodesWithFixedBits"), 2);
  ASSERT_EQ(stat("numFixedOps"), 1);

  // ite(c, 1 o p, 0 o q) = 11: while c selects the else branch, the target 11
  // has no consistent value in 0x (as in the engine test const_bits_conflict).
  Node c = nm->mkVar("c", nm->booleanType());
  Node p = nm->mkVar("p", nm->mkBitVectorType(1));
  Node q = nm->mkVar("q", nm->mkBitVectorType(1));
  Node h = nm->mkNode(
      Kind::EQUAL,
      nm->mkNode(
          Kind::ITE,
          c,
          nm->mkNode(Kind::BITVECTOR_CONCAT, nm->mkConst(BitVector(1, 1u)), p),
          nm->mkNode(Kind::BITVECTOR_CONCAT, nm->mkConst(BitVector(1, 0u)), q)),
      nm->mkConst(BitVector(2, 3u)));
  // Conflicts are rare (the condition is essential while it selects the else
  // branch), so try several seeds, each with its own engine.
  int64_t conflicts = 0;
  for (uint32_t seed = 0; seed < 20; ++seed)
  {
    SolverEngine slv(nm);
    slv.setOption("bv-ls-const-bits", "true");
    slv.setOption("seed", std::to_string(seed));
    slv.finishInit();
    BvLsSolver lsSeed(slv.getEnv());
    ASSERT_EQ(lsSeed.check({h}), prop::SAT_VALUE_TRUE);
    ASSERT_TRUE(lsSeed.getValue(c).getConst<bool>());
    StatisticsRegistry& r = slv.getEnv().getStatisticsRegistry();
    int64_t n = r.registerInt("theory::bv::ls::numConflicts").get();
    HistogramStat<LsKind> byKind =
        r.registerHistogram<LsKind>("theory::bv::ls::conflictsByKind");
    int64_t sum = 0;
    for (uint32_t k = 0; k < kNumLsKinds; ++k)
    {
      sum += byKind.getValue(static_cast<LsKind>(k));
    }
    ASSERT_EQ(sum, n) << "seed " << seed;
    ASSERT_EQ(static_cast<int64_t>(byKind.getValue(LsKind::ITE)), n);
    conflicts += n;
  }
  ASSERT_GT(conflicts, 0);
}

/** The adapter with --bv-ls-native-ops and --bv-ls-const-bits (prop-c+). */
class TestTheoryWhiteBvLsSolverNativeOps : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("bv-ls-const-bits", "true");
    d_slvEngine->setOption("bv-ls-native-ops", "true");
    d_slvEngine->finishInit();
  }

  /** A random constant of width w. */
  Node mkBv(uint32_t w)
  {
    Integer v;
    for (uint32_t i = 0; i < w; i += 32)
    {
      v = v.multiplyByPow2(32) + Integer(static_cast<uint32_t>(d_gen()));
    }
    return d_nodeManager->mkConst(BitVector(w, v.extractBitRange(w, 0)));
  }

  std::mt19937 d_gen{7};
};

/**
 * bvxor, bvashr and sign_extend become one native node each: over fresh
 * variables the translation adds the variables and that node only. On
 * constants the nodes fold to the value of the rewritten term.
 */
TEST_F(TestTheoryWhiteBvLsSolverNativeOps, native_nodes)
{
  ASSERT_TRUE(d_slvEngine->getOptions().bv.bvLsNativeOps);
  Env& env = d_slvEngine->getEnv();
  BvLsSolver ls(env);
  NodeManager* nm = d_nodeManager.get();
  TypeNode bv8 = nm->mkBitVectorType(8);
  Node x = nm->mkVar("x", bv8);
  Node y = nm->mkVar("y", bv8);
  uint32_t before = ls.d_engine.numNodes();
  ASSERT_TRUE(ls.translate(nm->mkNode(Kind::BITVECTOR_XOR, x, y)));
  ASSERT_EQ(ls.d_engine.numNodes(), before + 3);  // x, y, x ^ y
  ASSERT_TRUE(ls.translate(nm->mkNode(Kind::BITVECTOR_ASHR, x, y)));
  ASSERT_EQ(ls.d_engine.numNodes(), before + 4);
  ASSERT_TRUE(ls.translate(utils::mkSignExtend(x, 4)));
  ASSERT_EQ(ls.d_engine.numNodes(), before + 5);

  for (uint32_t w : {1u, 2u, 3u, 8u, 64u, 65u})
  {
    for (uint32_t i = 0; i < 30; ++i)
    {
      Node a = mkBv(w);
      Node b = mkBv(w);
      // Small amounts make the arithmetic shift interesting.
      Node k = nm->mkConst(BitVector(w, Integer(d_gen() % (w + 2)))
                               .unsignedRemTotal(BitVector::mkOnes(w)));
      for (const Node& t : {nm->mkNode(Kind::BITVECTOR_XOR, a, b),
                            nm->mkNode(Kind::BITVECTOR_XNOR, a, b),
                            nm->mkNode(Kind::BITVECTOR_ASHR, a, b),
                            nm->mkNode(Kind::BITVECTOR_ASHR, a, k),
                            utils::mkSignExtend(a, 5)})
      {
        std::optional<uint32_t> id = ls.translate(t);
        ASSERT_TRUE(id.has_value()) << t;
        ASSERT_TRUE(ls.d_engine.isConst(*id)) << t;
        Node expected = env.getRewriter()->rewrite(t);
        ASSERT_EQ(ls.d_engine.value(*id).toBitVector(),
                  expected.getConst<BitVector>())
            << t;
      }
    }
  }
}

/**
 * End to end with the native operators: x ^ y = a5, x >>a 2 = f9 (x is
 * 111001xx), 80 >>a s = f0 (s = 3), sext(a, 4) = fa (a = 1010) and y < 60.
 * The search finds a model and it satisfies the facts.
 */
TEST_F(TestTheoryWhiteBvLsSolverNativeOps, check_and_model)
{
  BvLsSolver ls(d_slvEngine->getEnv());
  NodeManager* nm = d_nodeManager.get();
  TypeNode bv8 = nm->mkBitVectorType(8);
  Node x = nm->mkVar("x", bv8);
  Node y = nm->mkVar("y", bv8);
  Node s = nm->mkVar("s", bv8);
  Node a = nm->mkVar("a", nm->mkBitVectorType(4));
  auto c8 = [nm](uint32_t v) { return nm->mkConst(BitVector(8, v)); };
  std::vector<Node> facts = {
      nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_XOR, x, y), c8(0xa5)),
      nm->mkNode(
          Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_ASHR, x, c8(2)), c8(0xf9)),
      nm->mkNode(
          Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_ASHR, c8(0x80), s), c8(0xf0)),
      nm->mkNode(Kind::EQUAL, utils::mkSignExtend(a, 4), c8(0xfa)),
      nm->mkNode(Kind::BITVECTOR_ULT, y, c8(0x60))};
  ASSERT_EQ(ls.check(facts), prop::SAT_VALUE_TRUE);
  BitVector xv = ls.getValue(x).getConst<BitVector>();
  BitVector yv = ls.getValue(y).getConst<BitVector>();
  ASSERT_EQ(xv ^ yv, BitVector(8, 0xa5u));
  ASSERT_EQ(xv.arithRightShift(BitVector(8, 2u)), BitVector(8, 0xf9u));
  ASSERT_EQ(ls.getValue(s).getConst<BitVector>(), BitVector(8, 3u));
  ASSERT_EQ(ls.getValue(a).getConst<BitVector>(), BitVector(4, 0xau));
  ASSERT_TRUE(yv < BitVector(8, 0x60u));
}

}  // namespace test
}  // namespace cvc5::internal
