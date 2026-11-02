/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Adapter between cvc5 and the local search engine: translates bit-vector
 * facts into an LsEngine DAG, runs the search, and answers model queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__BV_LS_SOLVER_H
#define CVC5__THEORY__BV__LS__BV_LS_SOLVER_H

#include <map>
#include <optional>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"
#include "theory/bv/ls/ls_engine.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

/**
 * Runs propagation-based local search on a conjunction of bit-vector facts.
 *
 * The facts are either eager atoms (BITVECTOR_EAGER_ATOM, one per assertion)
 * or the bit-vector literals of lazy mode. The translation to the engine's
 * base operators is memoized and persists across calls, together with the
 * values of the leaves, so incremental calls continue from the previous
 * assignment.
 */
class BvLsSolver : protected EnvObj
{
 public:
  BvLsSolver(Env& env);

  /**
   * Search for a model of the conjunction of facts. Return SAT_VALUE_TRUE if
   * one was found (and passed the self-check), SAT_VALUE_UNKNOWN otherwise:
   * on unsupported terms, when a budget runs out, or when a fact is false
   * and constant.
   */
  prop::SatValue check(const std::vector<Node>& facts);

  /**
   * Return the value of n in the last model if n is one of getLeaves(), and
   * null otherwise.
   */
  Node getValue(TNode n) const;

  /**
   * Return the variables that have a value in the local search model, in
   * creation order: the leaves (Boolean and bit-vector variables), and the
   * purification skolems that are translated as the terms they purify (see
   * option bvLsUnpurify).
   */
  const std::vector<Node>& getLeaves() const { return d_leaves; }

 private:
  /**
   * Return the engine node for n, translating its subterms first. Return
   * nothing if n contains an unsupported term.
   */
  std::optional<uint32_t> translate(TNode n);
  /** Translate n, whose children are already translated. */
  std::optional<uint32_t> translateOne(TNode n);
  /**
   * Add the roots of fact to roots: split top-level conjunctions (and negated
   * disjunctions) and translate each conjunct. Return false if a conjunct
   * contains an unsupported term.
   */
  bool collectRoots(TNode fact, std::vector<uint32_t>& roots);
  /**
   * Return the engine node of the term that the purification skolem k
   * purifies, if bvLsUnpurify is set, k is such a skolem and the term is
   * supported. Return nothing otherwise.
   */
  std::optional<uint32_t> translateUnpurified(TNode k);
  /**
   * Return true if n is the definition ite(c, k = a, k = b) of a purification
   * skolem k for ite(c, a, b). It holds once k is translated as ite(c, a, b),
   * so it need not be a root.
   */
  bool isPurifyDefinition(TNode n);
  /** Return true if every fact evaluates to true under the leaf values. */
  bool selfCheck(const std::vector<Node>& facts);

  /** Return the width of n in the local search (1 for Booleans). */
  static uint32_t width(TNode n);

  /* Helpers that build derived operators in the engine. */
  uint32_t mkNot(uint32_t a);
  uint32_t mkAnd(uint32_t a, uint32_t b);
  uint32_t mkOr(uint32_t a, uint32_t b);
  uint32_t mkXor(uint32_t a, uint32_t b);
  uint32_t mkExtract(uint32_t a, uint32_t hi, uint32_t lo);
  uint32_t mkConst(uint32_t w, const Integer& v);
  uint32_t mkConst(uint32_t w, uint32_t v) { return mkConst(w, Integer(v)); }
  /** a <s b, FMCAD'20 footnote 1. */
  uint32_t mkSlt(uint32_t a, uint32_t b, uint32_t w);
  /** Fold the n-ary operator k over ids from the left. */
  uint32_t mkFold(LsKind k, const std::vector<uint32_t>& ids);

  LsEngine d_engine;
  /** The engine node of each translated term. */
  std::unordered_map<Node, uint32_t> d_nodeMap;
  /** Constant leaves by (width, value), so equal constants share a node. */
  std::map<std::pair<uint32_t, Integer>, uint32_t> d_consts;
  /** See getLeaves(). */
  std::vector<Node> d_leaves;

  IntStat d_numChecks;
  IntStat d_numSat;
  IntStat d_numUnsupported;
  IntStat d_numUnpurified;
  IntStat d_numPurifyDefs;
  IntStat d_numSelfCheckFailed;
  IntStat d_numMoves;
  IntStat d_numProps;
  IntStat d_numPropsInv;
  IntStat d_numPropsCons;
  IntStat d_numUpdates;
  IntStat d_numConflicts;
  IntStat d_numRoots;
  IntStat d_numNodes;
  TimerStat d_timeTranslate;
  TimerStat d_timeSearch;
};

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__BV_LS_SOLVER_H */
