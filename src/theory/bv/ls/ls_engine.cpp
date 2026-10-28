/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * The propagation-based local search engine.
 */

#include "theory/bv/ls/ls_engine.h"

#include <algorithm>

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

LsEngine::LsEngine(uint64_t seed, LsConfig config)
    : d_config(config), d_rng(seed)
{
}

uint32_t LsEngine::mkLeaf(uint32_t width, std::optional<LsValue> constValue)
{
  Assert(width > 0);
  Assert(!constValue || constValue->getSize() == width);
  Node n;
  n.isConst = constValue.has_value();
  n.op.kind = n.isConst ? LsKind::CONST : LsKind::VAR;
  n.value = n.isConst ? *constValue : LsValue::mkZero(width);
  d_nodes.push_back(std::move(n));
  return d_nodes.size() - 1;
}

uint32_t LsEngine::mkOp(LsKind k,
                        const std::vector<uint32_t>& children,
                        uint32_t hi,
                        uint32_t lo)
{
  Assert(arity(k) > 0 && children.size() == arity(k));
  if (k != LsKind::EXTRACT)
  {
    hi = lo = 0;
  }
  // An ITE with a constant condition is its selected branch.
  if (k == LsKind::ITE && d_nodes[children[0]].isConst)
  {
    return d_nodes[children[0]].value.isBitSet(0) ? children[1] : children[2];
  }

  std::vector<uint32_t> key = {static_cast<uint32_t>(k), hi, lo};
  key.insert(key.end(), children.begin(), children.end());
  auto it = d_opCache.find(key);
  if (it != d_opCache.end())
  {
    return it->second;
  }

  Node n;
  n.op = {k, hi, lo};
  n.children = children;
  n.value = evaluate(n.op, childValues(n));
  bool allConst =
      std::all_of(children.begin(), children.end(), [this](uint32_t c) {
        return d_nodes[c].isConst;
      });
  uint32_t id;
  if (allConst)
  {
    id = mkLeaf(n.value.getSize(), n.value);
  }
  else
  {
    d_nodes.push_back(std::move(n));
    id = d_nodes.size() - 1;
  }
  d_opCache.emplace(std::move(key), id);
  return id;
}

void LsEngine::setRoots(const std::vector<uint32_t>& roots)
{
  d_roots.clear();
  std::vector<bool> seen(d_nodes.size(), false);
  for (uint32_t r : roots)
  {
    Assert(r < d_nodes.size());
    Assert(d_nodes[r].value.getSize() == 1) << "root of width > 1";
    if (!seen[r])
    {
      seen[r] = true;
      d_roots.push_back(r);
    }
  }
  d_rootsChanged = true;
}

std::vector<const LsValue*> LsEngine::childValues(const Node& n) const
{
  std::vector<const LsValue*> ch;
  ch.reserve(n.children.size());
  for (uint32_t c : n.children)
  {
    ch.push_back(&d_nodes[c].value);
  }
  return ch;
}

void LsEngine::reevaluate(uint32_t id)
{
  Node& n = d_nodes[id];
  if (!n.children.empty())
  {
    n.value = evaluate(n.op, childValues(n));
  }
}

void LsEngine::updateUnsat(uint32_t id)
{
  if (!d_isRoot[id])
  {
    return;
  }
  bool unsat = !d_nodes[id].value.isBitSet(0);
  int64_t pos = d_unsatPos[id];
  if (unsat && pos < 0)
  {
    d_unsatPos[id] = d_unsatRoots.size();
    d_unsatRoots.push_back(id);
  }
  else if (!unsat && pos >= 0)
  {
    uint32_t last = d_unsatRoots.back();
    d_unsatRoots[pos] = last;
    d_unsatPos[last] = pos;
    d_unsatRoots.pop_back();
    d_unsatPos[id] = -1;
  }
}

void LsEngine::prepareRoots()
{
  uint32_t size = d_nodes.size();
  d_isRoot.assign(size, false);
  d_unsatPos.assign(size, -1);
  d_unsatRoots.clear();
  d_parents.assign(size, {});
  d_coneMark.assign(size, 0);
  d_coneEpoch = 0;

  // The nodes reachable from the roots.
  std::vector<bool> reached(size, false);
  std::vector<uint32_t> stack;
  for (uint32_t r : d_roots)
  {
    d_isRoot[r] = true;
    if (!reached[r])
    {
      reached[r] = true;
      stack.push_back(r);
    }
  }
  std::vector<uint32_t> reachable;
  while (!stack.empty())
  {
    uint32_t id = stack.back();
    stack.pop_back();
    reachable.push_back(id);
    for (uint32_t c : d_nodes[id].children)
    {
      if (!reached[c])
      {
        reached[c] = true;
        stack.push_back(c);
      }
    }
  }

  // Parents and values, in topological (id) order.
  std::sort(reachable.begin(), reachable.end());
  for (uint32_t id : reachable)
  {
    const std::vector<uint32_t>& ch = d_nodes[id].children;
    for (size_t i = 0; i < ch.size(); ++i)
    {
      // A node with the same child twice is its parent once.
      if (std::find(ch.begin(), ch.begin() + i, ch[i]) == ch.begin() + i)
      {
        d_parents[ch[i]].push_back(id);
      }
    }
    reevaluate(id);
  }
  for (uint32_t r : d_roots)
  {
    updateUnsat(r);
  }
  d_rootsChanged = false;
}

LsResult LsEngine::solve(uint64_t maxProps,
                         uint64_t maxUpdates,
                         const std::function<bool()>& terminate)
{
  if (d_rootsChanged)
  {
    prepareRoots();
  }
  uint64_t propLimit = d_stats.props + maxProps;
  uint64_t updateLimit = d_stats.updates + maxUpdates;
  while (!d_unsatRoots.empty())
  {
    if ((maxProps > 0 && d_stats.props >= propLimit)
        || (maxUpdates > 0 && d_stats.updates >= updateLimit)
        || (terminate && terminate()))
    {
      return LsResult::UNKNOWN;
    }
    uint32_t r = d_unsatRoots[d_rng.pickIndex(d_unsatRoots.size())];
    if (d_nodes[r].isConst)
    {
      // A constant false root: leave it to bit-blasting to report.
      return LsResult::UNKNOWN;
    }
    std::optional<std::pair<uint32_t, LsValue>> move = selectMove(r);
    if (!move)
    {
      ++d_stats.conflicts;
      continue;
    }
    if (updateCone(move->first, move->second))
    {
      ++d_stats.moves;
    }
    if (d_checkInvariants)
    {
      AlwaysAssert(checkInvariants()) << "local search invariant violated";
    }
  }
  return LsResult::SAT;
}

std::optional<std::pair<uint32_t, LsValue>> LsEngine::selectMove(uint32_t r)
{
  LsValue t = LsValue::mkOne(1);
  uint32_t id = r;
  while (true)
  {
    const Node& n = d_nodes[id];
    if (n.op.kind == LsKind::VAR)
    {
      return std::make_pair(id, t);
    }
    if (n.isConst)
    {
      return std::nullopt;
    }
    std::vector<const LsValue*> ch = childValues(n);
    std::optional<std::pair<uint32_t, bool>> path = selectPath(n, t, ch);
    ++d_stats.props;
    if (!path)
    {
      return std::nullopt;
    }
    auto [i, onlyOne] = *path;
    if ((onlyOne || d_rng.pickWithProb(d_config.probInverse))
        && isInvertible(n.op, i, t, ch))
    {
      t = inverseValue(n.op, i, t, ch, d_rng);
      ++d_stats.propsInv;
    }
    else
    {
      t = consistentValue(n.op, i, t, ch, d_rng);
      ++d_stats.propsCons;
    }
    id = n.children[i];
  }
}

std::optional<std::pair<uint32_t, bool>> LsEngine::selectPath(
    const Node& n, const LsValue& t, const std::vector<const LsValue*>& ch)
{
  std::vector<uint32_t> inputs;
  for (uint32_t i = 0, size = n.children.size(); i < size; ++i)
  {
    if (d_nodes[n.children[i]].isConst)
    {
      continue;
    }
    // The disabled branch of an ITE is never a propagation path.
    if (n.op.kind == LsKind::ITE && i > 0 && ch[0]->isBitSet(0) != (i == 1))
    {
      continue;
    }
    inputs.push_back(i);
  }
  if (inputs.empty())
  {
    return std::nullopt;
  }
  if (inputs.size() == 1)
  {
    return std::make_pair(inputs[0], true);
  }
  if (d_rng.pickWithProb(d_config.probEssential))
  {
    std::vector<uint32_t> essential;
    for (uint32_t i : inputs)
    {
      if (isEssential(n.op, i, t, ch))
      {
        essential.push_back(i);
      }
    }
    if (!essential.empty())
    {
      return std::make_pair(essential[d_rng.pickIndex(essential.size())],
                            false);
    }
  }
  return std::make_pair(inputs[d_rng.pickIndex(inputs.size())], false);
}

bool LsEngine::updateCone(uint32_t leaf, const LsValue& v)
{
  Node& l = d_nodes[leaf];
  Assert(l.op.kind == LsKind::VAR);
  if (l.value == v)
  {
    return false;
  }
  l.value = v;
  ++d_stats.updates;
  updateUnsat(leaf);

  // Collect the ancestors of leaf, then re-evaluate them in id order.
  ++d_coneEpoch;
  std::vector<uint32_t> cone;
  std::vector<uint32_t> stack = {leaf};
  while (!stack.empty())
  {
    uint32_t id = stack.back();
    stack.pop_back();
    for (uint32_t p : d_parents[id])
    {
      if (d_coneMark[p] != d_coneEpoch)
      {
        d_coneMark[p] = d_coneEpoch;
        cone.push_back(p);
        stack.push_back(p);
      }
    }
  }
  std::sort(cone.begin(), cone.end());
  for (uint32_t id : cone)
  {
    reevaluate(id);
    updateUnsat(id);
  }
  d_stats.updates += cone.size();
  return true;
}

bool LsEngine::checkInvariants() const
{
  if (d_rootsChanged)
  {
    return false;
  }
  std::vector<bool> reached(d_nodes.size(), false);
  std::vector<uint32_t> stack(d_roots.begin(), d_roots.end());
  while (!stack.empty())
  {
    uint32_t id = stack.back();
    stack.pop_back();
    if (reached[id])
    {
      continue;
    }
    reached[id] = true;
    const Node& n = d_nodes[id];
    if (!n.children.empty() && evaluate(n.op, childValues(n)) != n.value)
    {
      return false;
    }
    stack.insert(stack.end(), n.children.begin(), n.children.end());
  }
  for (uint32_t r : d_roots)
  {
    bool unsat = !d_nodes[r].value.isBitSet(0);
    if (unsat != (d_unsatPos[r] >= 0))
    {
      return false;
    }
  }
  for (size_t i = 0; i < d_unsatRoots.size(); ++i)
  {
    uint32_t r = d_unsatRoots[i];
    if (!d_isRoot[r] || d_unsatPos[r] != static_cast<int64_t>(i))
    {
      return false;
    }
  }
  return true;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
