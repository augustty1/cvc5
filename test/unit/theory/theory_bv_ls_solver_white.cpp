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
#include "test_smt.h"
#include "theory/bv/ls/bv_ls_solver.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

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
      ASSERT_EQ(v, expected.getConst<BitVector>()) << term;
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

}  // namespace test
}  // namespace cvc5::internal
