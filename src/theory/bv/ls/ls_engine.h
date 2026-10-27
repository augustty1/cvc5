/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * The propagation-based local search engine (FMSD'17 Fig. 2): a DAG of
 * operator nodes over plain values, a set of roots, and the move loop.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_ENGINE_H
#define CVC5__THEORY__BV__LS__LS_ENGINE_H

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <vector>

#include "theory/bv/ls/ls_ops.h"
#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

/** The result of LsEngine::solve. */
enum class LsResult
{
  SAT,     // every root is true under the current assignment
  UNKNOWN  // a budget ran out, termination was requested, or a root is false
           // and constant
};

/** Counters of the engine, cumulative over all calls to solve. */
struct LsStats
{
  /** Moves made (a leaf received a new value). */
  uint64_t moves = 0;
  /** Down-propagation steps, including those of moves that end in a conflict.
   */
  uint64_t props = 0;
  /** Propagation steps that used an inverse value. */
  uint64_t propsInv = 0;
  /** Propagation steps that used a consistent value. */
  uint64_t propsCons = 0;
  /** Re-evaluated nodes, counting the leaf of each move. */
  uint64_t updates = 0;
  /** Moves that ended without a leaf to change. */
  uint64_t conflicts = 0;
};

/**
 * Probabilities (per mille) of the engine's random choices. The defaults are
 * Bitwuzla's; neither paper specifies them.
 */
struct LsConfig
{
  /** Try an inverse value (when invertible) instead of a consistent one. */
  uint32_t probInverse = 990;
  /** Restrict path selection to essential inputs, if there are any. */
  uint32_t probEssential = 990;
};

/**
 * The engine. Nodes are created with mkLeaf and mkOp and identified by ids
 * assigned in creation order; since children are created before their
 * parents, id order is a topological order. Nodes are never deleted, and leaf
 * values persist across calls to solve, which is what incremental solving
 * relies on.
 */
class LsEngine
{
 public:
  explicit LsEngine(uint64_t seed, LsConfig config = {});

  /**
   * Create a leaf of the given width: a constant if constValue is given,
   * otherwise a variable with initial value 0.
   */
  uint32_t mkLeaf(uint32_t width, std::optional<LsValue> constValue);

  /**
   * Return the node for op applied to the given children. Identical requests
   * return the same node. If all children are constants, the result is a
   * constant leaf; an ITE with a constant condition is its selected branch.
   */
  uint32_t mkOp(LsKind k,
                const std::vector<uint32_t>& children,
                uint32_t hi = 0,
                uint32_t lo = 0);

  /** Replace the set of roots. Each root must have width 1. */
  void setRoots(const std::vector<uint32_t>& roots);

  /**
   * Search for an assignment that makes every root true. Each budget is the
   * number of steps allowed in this call (0 = unlimited): maxProps limits
   * propagation steps and maxUpdates re-evaluated nodes. terminate, if set, is
   * polled before each move.
   */
  LsResult solve(uint64_t maxProps,
                 uint64_t maxUpdates,
                 const std::function<bool()>& terminate = nullptr);

  /** Return the current value of node id. */
  const LsValue& value(uint32_t id) const { return d_nodes[id].value; }

  /** Return true if node id is a constant leaf. */
  bool isConst(uint32_t id) const { return d_nodes[id].isConst; }

  /** Return the number of nodes. */
  uint32_t numNodes() const { return d_nodes.size(); }

  /** Return the number of roots that are currently false. */
  uint32_t numUnsatRoots() const { return d_unsatRoots.size(); }

  const LsStats& stats() const { return d_stats; }

  /** Check the engine invariants after every move (expensive). */
  void setCheckInvariants(bool on) { d_checkInvariants = on; }

  /**
   * Return true if every node reachable from the roots equals the evaluation
   * of its children, and the unsat roots are exactly the roots whose value is
   * 0. Requires the roots to be prepared (solve was called since the last
   * setRoots).
   */
  bool checkInvariants() const;

 private:
  struct Node
  {
    OpInfo op;
    std::vector<uint32_t> children;
    LsValue value;
    bool isConst = false;
  };

  /** Rebuild the parents, values and unsat roots after the roots changed. */
  void prepareRoots();
  /** Return the children values of n, in order. */
  std::vector<const LsValue*> childValues(const Node& n) const;
  /** Recompute the value of node id from its children. */
  void reevaluate(uint32_t id);
  /** Add or remove root id from the unsat roots according to its value. */
  void updateUnsat(uint32_t id);

  /**
   * Propagate target value 1 down from root r. Return the leaf to change and
   * its new value, or nothing on a conflict.
   */
  std::optional<std::pair<uint32_t, LsValue>> selectMove(uint32_t r);
  /**
   * Select the child of n to propagate t to. Return its position, and whether
   * it is the only candidate; nothing if there is no candidate.
   */
  std::optional<std::pair<uint32_t, bool>> selectPath(
      const Node& n, const LsValue& t, const std::vector<const LsValue*>& ch);
  /** Set leaf to v and re-evaluate its cone. */
  void updateCone(uint32_t leaf, const LsValue& v);

  LsConfig d_config;
  LsRng d_rng;
  std::vector<Node> d_nodes;
  /** Hash-consing of operator nodes: (kind, hi, lo, children) to id. */
  std::map<std::vector<uint32_t>, uint32_t> d_opCache;

  std::vector<uint32_t> d_roots;
  bool d_rootsChanged = false;
  std::vector<bool> d_isRoot;
  /** The roots whose value is 0, with the position of each in d_unsatPos. */
  std::vector<uint32_t> d_unsatRoots;
  std::vector<int64_t> d_unsatPos;
  /** Parents of each node reachable from the roots. */
  std::vector<std::vector<uint32_t>> d_parents;

  /** Scratch space of updateCone. */
  std::vector<uint32_t> d_coneMark;
  uint32_t d_coneEpoch = 0;

  LsStats d_stats;
  bool d_checkInvariants = false;
};

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_ENGINE_H */
