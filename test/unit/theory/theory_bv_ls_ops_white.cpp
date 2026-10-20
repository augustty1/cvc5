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

#include "test.h"
#include "theory/bv/ls/ls_ops.h"
#include "theory/bv/ls/ls_value.h"

namespace cvc5::internal {

using namespace theory::bv::ls;

namespace test {

class TestTheoryWhiteBvLsOps : public TestInternal
{
};

/** Placeholder: checks that the LS headers compile and link into a test. */
TEST_F(TestTheoryWhiteBvLsOps, skeleton)
{
  LsValue v(4, 5u);
  ASSERT_EQ(v.getSize(), 4u);
}

}  // namespace test
}  // namespace cvc5::internal
