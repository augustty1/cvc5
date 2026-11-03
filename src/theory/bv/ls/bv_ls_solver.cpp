/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Adapter between cvc5 and the local search engine.
 */

#include "theory/bv/ls/bv_ls_solver.h"

#include "expr/skolem_manager.h"
#include "options/bv_options.h"
#include "options/main_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

namespace {

LsConfig mkConfig(const Options& opts)
{
  LsConfig config;
  config.probInverse = opts.bv.bvLsProbInv;
  config.probEssential = opts.bv.bvLsProbEss;
  return config;
}

}  // namespace

BvLsSolver::BvLsSolver(Env& env)
    : EnvObj(env),
      d_engine(options().driver.seed, mkConfig(options())),
      d_numChecks(
          statisticsRegistry().registerInt("theory::bv::ls::numChecks")),
      d_numSat(statisticsRegistry().registerInt("theory::bv::ls::numSat")),
      d_numUnsupported(
          statisticsRegistry().registerInt("theory::bv::ls::numUnsupported")),
      d_numUnpurified(
          statisticsRegistry().registerInt("theory::bv::ls::numUnpurified")),
      d_numPurifyDefs(
          statisticsRegistry().registerInt("theory::bv::ls::numPurifyDefs")),
      d_numSelfCheckFailed(statisticsRegistry().registerInt(
          "theory::bv::ls::numSelfCheckFailed")),
      d_numMoves(statisticsRegistry().registerInt("theory::bv::ls::numMoves")),
      d_numProps(statisticsRegistry().registerInt("theory::bv::ls::numProps")),
      d_numPropsInv(
          statisticsRegistry().registerInt("theory::bv::ls::numPropsInv")),
      d_numPropsCons(
          statisticsRegistry().registerInt("theory::bv::ls::numPropsCons")),
      d_numUpdates(
          statisticsRegistry().registerInt("theory::bv::ls::numUpdates")),
      d_numConflicts(
          statisticsRegistry().registerInt("theory::bv::ls::numConflicts")),
      d_numRoots(statisticsRegistry().registerInt("theory::bv::ls::numRoots")),
      d_numNodes(statisticsRegistry().registerInt("theory::bv::ls::numNodes")),
      d_timeTranslate(
          statisticsRegistry().registerTimer("theory::bv::ls::timeTranslate")),
      d_timeSearch(
          statisticsRegistry().registerTimer("theory::bv::ls::timeSearch"))
{
}

prop::SatValue BvLsSolver::check(const std::vector<Node>& facts)
{
  ++d_numChecks;
  std::vector<uint32_t> roots;
  {
    CodeTimer timer(d_timeTranslate);
    for (const Node& fact : facts)
    {
      if (!collectRoots(fact, roots))
      {
        Trace("bv-ls") << "bv-ls: unsupported fact " << fact << std::endl;
        ++d_numUnsupported;
        return prop::SAT_VALUE_UNKNOWN;
      }
    }
  }
  d_engine.setRoots(roots);
  d_numRoots = roots.size();
  d_numNodes = d_engine.numNodes();
  Trace("bv-ls") << "bv-ls: " << facts.size() << " facts, " << roots.size()
                 << " roots, " << d_engine.numNodes() << " nodes" << std::endl;

  LsStats before = d_engine.stats();
  LsResult res;
  {
    CodeTimer timer(d_timeSearch);
    ResourceManager* rm = resourceManager();
    res = d_engine.solve(options().bv.bvLsNprops,
                         options().bv.bvLsNupdates,
                         [rm]() { return rm->out(); });
  }
  const LsStats& after = d_engine.stats();
  d_numMoves += after.moves - before.moves;
  d_numProps += after.props - before.props;
  d_numPropsInv += after.propsInv - before.propsInv;
  d_numPropsCons += after.propsCons - before.propsCons;
  d_numUpdates += after.updates - before.updates;
  d_numConflicts += after.conflicts - before.conflicts;
  Trace("bv-ls") << "bv-ls: " << (res == LsResult::SAT ? "sat" : "unknown")
                 << " after " << (after.props - before.props) << " props, "
                 << (after.moves - before.moves) << " moves" << std::endl;

  if (res != LsResult::SAT)
  {
    return prop::SAT_VALUE_UNKNOWN;
  }
  if (!selfCheck(facts))
  {
    ++d_numSelfCheckFailed;
    Assert(false) << "bv-ls: model does not satisfy the facts";
    return prop::SAT_VALUE_UNKNOWN;
  }
  ++d_numSat;
  return prop::SAT_VALUE_TRUE;
}

Node BvLsSolver::getValue(TNode n) const
{
  if (!n.isVar())
  {
    return Node::null();
  }
  auto it = d_nodeMap.find(n);
  if (it == d_nodeMap.end())
  {
    return Node::null();
  }
  const LsValue& v = d_engine.value(it->second);
  NodeManager* nm = nodeManager();
  if (n.getType().isBoolean())
  {
    return nm->mkConst(v.isBitSet(0));
  }
  return nm->mkConst(v.toBitVector());
}

bool BvLsSolver::selfCheck(const std::vector<Node>& facts)
{
  std::vector<Node> vals;
  vals.reserve(d_leaves.size());
  for (const Node& leaf : d_leaves)
  {
    vals.push_back(getValue(leaf));
  }
  for (const Node& fact : facts)
  {
    Node f = fact.getKind() == Kind::BITVECTOR_EAGER_ATOM ? fact[0] : fact;
    Node res = evaluate(f, d_leaves, vals);
    if (res.isNull() || !res.isConst())
    {
      res = rewrite(f.substitute(
          d_leaves.begin(), d_leaves.end(), vals.begin(), vals.end()));
    }
    if (!res.isConst() || !res.getConst<bool>())
    {
      Trace("bv-ls") << "bv-ls: self-check failed on " << fact << ", got "
                     << res << std::endl;
      return false;
    }
  }
  return true;
}

uint32_t BvLsSolver::width(TNode n)
{
  TypeNode tn = n.getType();
  return tn.isBoolean() ? 1 : tn.getBitVectorSize();
}

bool BvLsSolver::collectRoots(TNode fact, std::vector<uint32_t>& roots)
{
  // (node, negated) pairs still to split.
  std::vector<std::pair<TNode, bool>> stack = {
      {fact.getKind() == Kind::BITVECTOR_EAGER_ATOM ? fact[0] : fact, false}};
  while (!stack.empty())
  {
    auto [n, neg] = stack.back();
    stack.pop_back();
    Kind k = n.getKind();
    if (k == Kind::NOT)
    {
      stack.emplace_back(n[0], !neg);
      continue;
    }
    if ((k == Kind::AND && !neg) || (k == Kind::OR && neg))
    {
      for (const Node& c : n)
      {
        stack.emplace_back(c, neg);
      }
      continue;
    }
    if (!neg && isPurifyDefinition(n))
    {
      ++d_numPurifyDefs;
      continue;
    }
    std::optional<uint32_t> id = translate(n);
    if (!id)
    {
      return false;
    }
    uint32_t root = neg ? mkNot(*id) : *id;
    if (d_engine.isConst(root) && d_engine.value(root).isBitSet(0))
    {
      continue;  // true
    }
    roots.push_back(root);
  }
  return true;
}

std::optional<uint32_t> BvLsSolver::translateUnpurified(TNode k)
{
  if (!options().bv.bvLsUnpurify || !k.isVar())
  {
    return std::nullopt;
  }
  Node def = SkolemManager::getUnpurifiedForm(k);
  if (def == k)
  {
    return std::nullopt;
  }
  // def may contain other purification skolems, but not k, so this
  // recursion terminates.
  return translate(def);
}

bool BvLsSolver::isPurifyDefinition(TNode n)
{
  if (!options().bv.bvLsUnpurify || n.getKind() != Kind::ITE
      || n[1].getKind() != Kind::EQUAL || n[2].getKind() != Kind::EQUAL)
  {
    return false;
  }
  // Compare engine nodes rather than terms: the definition was rewritten
  // after purification, and its condition may mention purification skolems
  // where def mentions the terms they purify.
  auto same = [this](TNode x, TNode y) {
    std::optional<uint32_t> ix = translate(x);
    return ix && ix == translate(y);
  };
  for (uint32_t i = 0; i < 2; ++i)
  {
    TNode k = n[1][i];
    Node def = SkolemManager::getUnpurifiedForm(k);
    if (def == k || def.getKind() != Kind::ITE || !same(k, def))
    {
      continue;
    }
    TNode a = n[1][1 - i];
    uint32_t j = n[2][0] == k ? 1 : 0;
    if (n[2][1 - j] != k)
    {
      continue;
    }
    TNode b = n[2][j];
    // n is ite(c, k = a, k = b) with k translated as ite(c, a, b).
    if (same(n[0], def[0]) && same(a, def[1]) && same(b, def[2]))
    {
      return true;
    }
  }
  return false;
}

std::optional<uint32_t> BvLsSolver::translate(TNode n)
{
  // Iterative post-order: SMT-LIB DAGs can be too deep for recursion.
  std::vector<std::pair<TNode, bool>> stack = {{n, false}};
  while (!stack.empty())
  {
    auto [cur, childrenDone] = stack.back();
    stack.pop_back();
    if (d_nodeMap.find(cur) != d_nodeMap.end())
    {
      continue;
    }
    if (!childrenDone)
    {
      stack.emplace_back(cur, true);
      for (const Node& c : cur)
      {
        if (d_nodeMap.find(c) == d_nodeMap.end())
        {
          stack.emplace_back(c, false);
        }
      }
      continue;
    }
    std::optional<uint32_t> id = translateOne(cur);
    if (!id)
    {
      Trace("bv-ls") << "bv-ls: unsupported term " << cur << std::endl;
      return std::nullopt;
    }
    d_nodeMap.emplace(cur, *id);
  }
  return d_nodeMap.at(n);
}

std::optional<uint32_t> BvLsSolver::translateOne(TNode n)
{
  TypeNode tn = n.getType();
  if (!tn.isBoolean() && !tn.isBitVector())
  {
    return std::nullopt;
  }
  Kind k = n.getKind();
  uint32_t w = width(n);
  if (k == Kind::CONST_BITVECTOR)
  {
    return mkConst(w, n.getConst<BitVector>().getValue());
  }
  if (k == Kind::CONST_BOOLEAN)
  {
    return mkConst(1, n.getConst<bool>() ? 1u : 0u);
  }
  if (n.isVar())
  {
    d_leaves.push_back(n);
    if (std::optional<uint32_t> id = translateUnpurified(n))
    {
      ++d_numUnpurified;
      return id;
    }
    return d_engine.mkLeaf(w, std::nullopt);
  }

  std::vector<uint32_t> ch;
  for (const Node& c : n)
  {
    if (!c.getType().isBoolean() && !c.getType().isBitVector())
    {
      return std::nullopt;
    }
    ch.push_back(d_nodeMap.at(c));
  }
  switch (k)
  {
    case Kind::NOT:
    case Kind::BITVECTOR_NOT: return mkNot(ch[0]);
    case Kind::AND:
    case Kind::BITVECTOR_AND: return mkFold(LsKind::AND, ch);
    case Kind::OR:
    case Kind::BITVECTOR_OR:
    {
      uint32_t res = ch[0];
      for (size_t i = 1; i < ch.size(); ++i)
      {
        res = mkOr(res, ch[i]);
      }
      return res;
    }
    case Kind::IMPLIES: return mkNot(mkAnd(ch[0], mkNot(ch[1])));
    case Kind::XOR: return mkNot(d_engine.mkOp(LsKind::EQ, {ch[0], ch[1]}));
    case Kind::BITVECTOR_XOR:
    case Kind::BITVECTOR_XNOR:
    {
      uint32_t res = ch[0];
      for (size_t i = 1; i < ch.size(); ++i)
      {
        res = mkXor(res, ch[i]);
      }
      return k == Kind::BITVECTOR_XOR ? res : mkNot(res);
    }
    case Kind::BITVECTOR_NAND: return mkNot(mkAnd(ch[0], ch[1]));
    case Kind::BITVECTOR_NOR: return mkNot(mkOr(ch[0], ch[1]));
    case Kind::EQUAL:
    case Kind::BITVECTOR_COMP: return d_engine.mkOp(LsKind::EQ, ch);
    case Kind::ITE:
    case Kind::BITVECTOR_ITE: return d_engine.mkOp(LsKind::ITE, ch);

    case Kind::BITVECTOR_ULT:
    case Kind::BITVECTOR_ULTBV: return d_engine.mkOp(LsKind::ULT, ch);
    case Kind::BITVECTOR_UGT: return d_engine.mkOp(LsKind::ULT, {ch[1], ch[0]});
    case Kind::BITVECTOR_ULE:
      return mkNot(d_engine.mkOp(LsKind::ULT, {ch[1], ch[0]}));
    case Kind::BITVECTOR_UGE:
      return mkNot(d_engine.mkOp(LsKind::ULT, {ch[0], ch[1]}));
    case Kind::BITVECTOR_SLT:
    case Kind::BITVECTOR_SLTBV: return mkSlt(ch[0], ch[1], width(n[0]));
    case Kind::BITVECTOR_SGT: return mkSlt(ch[1], ch[0], width(n[0]));
    case Kind::BITVECTOR_SLE: return mkNot(mkSlt(ch[1], ch[0], width(n[0])));
    case Kind::BITVECTOR_SGE: return mkNot(mkSlt(ch[0], ch[1], width(n[0])));

    case Kind::BITVECTOR_ADD: return mkFold(LsKind::ADD, ch);
    case Kind::BITVECTOR_MULT: return mkFold(LsKind::MUL, ch);
    case Kind::BITVECTOR_NEG:
      return d_engine.mkOp(LsKind::ADD, {mkNot(ch[0]), mkConst(w, 1)});
    case Kind::BITVECTOR_SUB:
    {
      uint32_t neg = d_engine.mkOp(LsKind::ADD, {mkNot(ch[1]), mkConst(w, 1)});
      return d_engine.mkOp(LsKind::ADD, {ch[0], neg});
    }
    case Kind::BITVECTOR_UDIV: return d_engine.mkOp(LsKind::UDIV, ch);
    case Kind::BITVECTOR_UREM: return d_engine.mkOp(LsKind::UREM, ch);
    case Kind::BITVECTOR_SHL: return d_engine.mkOp(LsKind::SHL, ch);
    case Kind::BITVECTOR_LSHR: return d_engine.mkOp(LsKind::LSHR, ch);
    case Kind::BITVECTOR_ASHR:
    {
      // msb(a) ? ~(~a >> b) : a >> b
      uint32_t msb = mkExtract(ch[0], w - 1, w - 1);
      uint32_t neg = mkNot(d_engine.mkOp(LsKind::LSHR, {mkNot(ch[0]), ch[1]}));
      uint32_t pos = d_engine.mkOp(LsKind::LSHR, ch);
      return d_engine.mkOp(LsKind::ITE, {msb, neg, pos});
    }

    case Kind::BITVECTOR_CONCAT: return mkFold(LsKind::CONCAT, ch);
    case Kind::BITVECTOR_EXTRACT:
      return mkExtract(
          ch[0], utils::getExtractHigh(n), utils::getExtractLow(n));
    case Kind::BITVECTOR_BIT:
    {
      uint32_t i = n.getOperator().getConst<BitVectorBit>().d_bitIndex;
      return mkExtract(ch[0], i, i);
    }
    case Kind::BITVECTOR_ZERO_EXTEND:
    case Kind::BITVECTOR_SIGN_EXTEND:
    {
      uint32_t wa = width(n[0]);
      uint32_t m = w - wa;
      if (m == 0)
      {
        return ch[0];
      }
      uint32_t ext;
      if (k == Kind::BITVECTOR_ZERO_EXTEND)
      {
        ext = mkConst(m, 0);
      }
      else
      {
        Integer ones = Integer(2).pow(m) - 1;
        ext = d_engine.mkOp(LsKind::ITE,
                            {mkExtract(ch[0], wa - 1, wa - 1),
                             mkConst(m, ones),
                             mkConst(m, 0)});
      }
      return d_engine.mkOp(LsKind::CONCAT, {ext, ch[0]});
    }
    case Kind::BITVECTOR_REPEAT:
    {
      uint32_t times = w / width(n[0]);
      return mkFold(LsKind::CONCAT, std::vector<uint32_t>(times, ch[0]));
    }
    case Kind::BITVECTOR_ROTATE_LEFT:
    case Kind::BITVECTOR_ROTATE_RIGHT:
    {
      uint32_t amount = k == Kind::BITVECTOR_ROTATE_LEFT
                            ? n.getOperator()
                                  .getConst<BitVectorRotateLeft>()
                                  .d_rotateLeftAmount
                            : n.getOperator()
                                  .getConst<BitVectorRotateRight>()
                                  .d_rotateRightAmount;
      amount %= w;
      if (amount == 0)
      {
        return ch[0];
      }
      if (k == Kind::BITVECTOR_ROTATE_RIGHT)
      {
        amount = w - amount;
      }
      // Rotate left by amount: the low w-amount bits move to the top.
      return d_engine.mkOp(LsKind::CONCAT,
                           {mkExtract(ch[0], w - 1 - amount, 0),
                            mkExtract(ch[0], w - 1, w - amount)});
    }
    case Kind::BITVECTOR_REDOR:
      return mkNot(d_engine.mkOp(LsKind::EQ, {ch[0], mkConst(width(n[0]), 0)}));
    case Kind::BITVECTOR_REDAND:
    {
      uint32_t wa = width(n[0]);
      return d_engine.mkOp(LsKind::EQ,
                           {ch[0], mkConst(wa, Integer(2).pow(wa) - 1)});
    }
    default: break;
  }
  return std::nullopt;
}

uint32_t BvLsSolver::mkNot(uint32_t a)
{
  return d_engine.mkOp(LsKind::NOT, {a});
}

uint32_t BvLsSolver::mkAnd(uint32_t a, uint32_t b)
{
  return d_engine.mkOp(LsKind::AND, {a, b});
}

uint32_t BvLsSolver::mkOr(uint32_t a, uint32_t b)
{
  return mkNot(mkAnd(mkNot(a), mkNot(b)));
}

uint32_t BvLsSolver::mkXor(uint32_t a, uint32_t b)
{
  return mkAnd(mkNot(mkAnd(a, b)), mkNot(mkAnd(mkNot(a), mkNot(b))));
}

uint32_t BvLsSolver::mkExtract(uint32_t a, uint32_t hi, uint32_t lo)
{
  return d_engine.mkOp(LsKind::EXTRACT, {a}, hi, lo);
}

uint32_t BvLsSolver::mkConst(uint32_t w, const Integer& v)
{
  auto [it, inserted] = d_consts.emplace(std::make_pair(w, v), 0);
  if (inserted)
  {
    it->second = d_engine.mkLeaf(w, LsValue(w, v));
  }
  return it->second;
}

uint32_t BvLsSolver::mkSlt(uint32_t a, uint32_t b, uint32_t w)
{
  if (w == 1)
  {
    // a <s b iff a = 1 (-1) and b = 0.
    return mkAnd(a, mkNot(b));
  }
  uint32_t msbA = mkExtract(a, w - 1, w - 1);
  uint32_t msbB = mkExtract(b, w - 1, w - 1);
  uint32_t restA = mkExtract(a, w - 2, 0);
  uint32_t restB = mkExtract(b, w - 2, 0);
  return mkOr(d_engine.mkOp(LsKind::ULT, {msbB, msbA}),
              mkAnd(d_engine.mkOp(LsKind::EQ, {msbA, msbB}),
                    d_engine.mkOp(LsKind::ULT, {restA, restB})));
}

uint32_t BvLsSolver::mkFold(LsKind k, const std::vector<uint32_t>& ids)
{
  uint32_t res = ids[0];
  for (size_t i = 1; i < ids.size(); ++i)
  {
    res = d_engine.mkOp(k, {res, ids[i]});
  }
  return res;
}

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
