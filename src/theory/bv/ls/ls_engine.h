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

#include <array>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <vector>

#include "theory/bv/ls/ls_domain.h"
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
  /**
   * Moves made, i.e., leaves that received a new value. A propagation that
   * ends at a leaf with its current value is not a move (FMSD'17 Sec. 4).
   */
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
  /**
   * Moves that ended without a leaf to change: no child of a node could be
   * selected, or, with constant bits, no consistent value matched the domain
   * of the selected child (FMCAD'20 Fig. 2, lines 5-6).
   */
  uint64_t conflicts = 0;
  /** The conflicts by the kind of the node where they happened. */
  std::array<uint64_t, kNumLsKinds> conflictsByKind{};
  /**
   * prop-cb+: propagation steps that tried an inverse value and found bounds
   * for it; of those, the ones whose inverse value was drawn within the
   * bounds, and the ones whose bounds left no inverse value and fell back to
   * a consistent value. A run without any step with bounds draws the same
   * random numbers as without ineqBounds.
   */
  uint64_t propsWithBounds = 0;
  uint64_t propsBounded = 0;
  uint64_t boundsFallback = 0;
  /**
   * prop-cb+: inverse steps over a sign extension with sextRanges, and the
   * ones whose value was drawn among the sign extensions. A run without any
   * step with bounds or over a sign extension draws the same random numbers
   * as without these options.
   */
  uint64_t propsWithSext = 0;
  uint64_t propsSextRange = 0;
};

/**
 * The constant bits of the nodes reachable from the roots, over the nodes that
 * are not constant leaves. Computed when the roots are prepared.
 */
struct LsDomainStats
{
  /** Operator nodes whose domain has some fixed bit. */
  uint64_t nodesWithFixedBits = 0;
  /** Fixed bits, summed over the nodes. */
  uint64_t bitsFixed = 0;
  /** Bits, summed over the nodes. */
  uint64_t bitsTotal = 0;
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
  /**
   * Use constant bits (prop-c, FMCAD'20 Sec. IV): every operator node gets the
   * domain that forwardDomain computes from its children, a node whose domain
   * is fixed is a constant, and path and value selection use the rules modulo
   * constant bits, with conflicts. Without it every operator node has the
   * domain without fixed bits and the engine is the base local search, with
   * the same random draws.
   */
  bool constBits = false;
  /**
   * Draw the inverse values of inequalities within the bounds given by the
   * satisfied inequality roots on the same operand (prop-cb+, FMCAD'20 Sec.
   * V-A). Only with constBits.
   */
  bool ineqBounds = false;
  /**
   * Draw the inverse values of an inequality whose operand is a sign
   * extension among the sign extensions (the ranges (3) and (4) of FMCAD'20
   * Sec. V-A). Only with constBits.
   */
  bool sextRanges = false;
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
   * With constant bits, a node whose domain is fixed is also a constant leaf:
   * no assignment can change its value (plan D14). hi and lo are the indices
   * of EXTRACT; for SEXT, hi is the number of bits added; otherwise they are
   * ignored.
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

  /**
   * Return the stored value of node id. The moves keep it up to date only
   * for leaves and for the nodes reachable from the roots; see currentValue.
   */
  const LsValue& value(uint32_t id) const { return d_nodes[id].value; }

  /**
   * Return the value of node id under the current values of the leaves. For a
   * leaf or a node reachable from the prepared roots this is value(id); for
   * any other node it is computed from the leaves, since the moves do not
   * update it. Such a node is, e.g., the definition of a purification skolem
   * whose uses were all simplified to constants.
   */
  LsValue currentValue(uint32_t id) const;

  /** Return true if node id is a constant leaf. */
  bool isConst(uint32_t id) const { return d_nodes[id].isConst; }

  /**
   * Return the domain of node id: fixed for a constant, without fixed bits for
   * a variable, and for an operator the domain computed from its children
   * with constant bits, or the one without fixed bits otherwise. The value of
   * the node always matches it.
   */
  const TernaryDomain& domain(uint32_t id) const { return d_nodes[id].dom; }

  /** Return the constant bits of the nodes reachable from the roots. */
  const LsDomainStats& domainStats() const { return d_domainStats; }

  /**
   * Return the number of operator nodes that became constants because their
   * domain is fixed although some child is not a constant (D20).
   */
  uint64_t numFixedOps() const { return d_numFixedOps; }

  /** Return the number of nodes. */
  uint32_t numNodes() const { return d_nodes.size(); }

  /** Return the number of roots that are currently false. */
  uint32_t numUnsatRoots() const { return d_unsatRoots.size(); }

  /**
   * Return true if node id is an inequality asserted by the prepared roots
   * with the given polarity: an ULT that is a root (positive) or the child of
   * a NOT root (negative). Only computed with ineqBounds (prop-cb+, FMCAD'20
   * Sec. V-A); false otherwise.
   */
  bool isIneqRoot(uint32_t id, bool positive) const
  {
    return id < d_ineqRoot.size()
           && (d_ineqRoot[id] & (positive ? kIneqPos : kIneqNeg)) != 0;
  }

  /**
   * Return the bounds of node id from the inequalities of kind k: the
   * intersection of the solutions of the asserted inequalities of kind k on
   * id that hold with their polarity under the current values (prop-cb+,
   * FMCAD'20 Sec. V-A). Nothing if there is no such inequality or the
   * intersection is every value. The current value of id is always within
   * the bounds. Requires the prepared roots; nothing without ineqBounds.
   */
  std::optional<LsBounds> ineqBounds(uint32_t id, LsKind k) const;

  /**
   * Return k if node id is the sign extension of a k-bit node: a SEXT, or
   * the encoding of the adapter, concat(ite(y[k-1], ones, 0), y). Return 0
   * otherwise.
   */
  uint32_t sextWidth(uint32_t id) const;

  const LsStats& stats() const { return d_stats; }

  /** Check the engine invariants after every move (expensive). */
  void setCheckInvariants(bool on) { d_checkInvariants = on; }

  /**
   * Return true if every node reachable from the roots equals the evaluation
   * of its children and matches its domain, and the unsat roots are exactly
   * the roots whose value is 0. Requires the roots to be prepared (solve was
   * called since the last setRoots).
   */
  bool checkInvariants() const;

 private:
  struct Node
  {
    OpInfo op;
    std::vector<uint32_t> children;
    LsValue value;
    TernaryDomain dom;
    bool isConst = false;
  };

  /** Rebuild the parents, values and unsat roots after the roots changed. */
  void prepareRoots();
  /** Return the children values of n, in order. */
  LsChildren childValues(const Node& n) const;
  /** Return the children domains of n, in order. */
  LsDomains childDomains(const Node& n) const;
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
  std::optional<std::pair<uint32_t, bool>> selectPath(const Node& n,
                                                      const LsValue& t,
                                                      const LsChildren& ch);
  /**
   * Set leaf to v and re-evaluate its cone. Return false, and change nothing,
   * if leaf already has value v.
   */
  bool updateCone(uint32_t leaf, const LsValue& v);

  LsConfig d_config;
  LsRng d_rng;
  std::vector<Node> d_nodes;
  /** Hash-consing of operator nodes: (kind, hi, lo, children) to id. */
  std::map<std::vector<uint32_t>, uint32_t> d_opCache;

  std::vector<uint32_t> d_roots;
  bool d_rootsChanged = false;
  /** The nodes reachable from the roots when they were last prepared. */
  std::vector<bool> d_reachable;
  std::vector<bool> d_isRoot;
  /** The roots whose value is 0, with the position of each in d_unsatPos. */
  std::vector<uint32_t> d_unsatRoots;
  std::vector<int64_t> d_unsatPos;
  /** Parents of each node reachable from the roots. */
  std::vector<std::vector<uint32_t>> d_parents;
  /** The polarities with which each node is an asserted inequality. */
  static constexpr uint8_t kIneqPos = 1;
  static constexpr uint8_t kIneqNeg = 2;
  std::vector<uint8_t> d_ineqRoot;

  /**
   * Scratch space of updateCone: the cone being collected, the nodes whose
   * parents are still to be visited, and the mark of the nodes already in the
   * cone (those with d_coneMark equal to d_coneEpoch).
   */
  std::vector<uint32_t> d_cone;
  std::vector<uint32_t> d_coneStack;
  std::vector<uint32_t> d_coneMark;
  uint32_t d_coneEpoch = 0;

  LsStats d_stats;
  LsDomainStats d_domainStats;
  uint64_t d_numFixedOps = 0;
  bool d_checkInvariants = false;
};

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_ENGINE_H */
