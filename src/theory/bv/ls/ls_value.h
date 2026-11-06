/******************************************************************************
 * This file is part of a fork of the cvc5 project that adds
 * propagation-based local search for bit-vectors.
 *
 * Authors: Augusto Guerra, Heitor Leite
 * ****************************************************************************
 *
 * Values and randomness for propagation-based local search over bit-vectors.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__LS__LS_VALUE_H
#define CVC5__THEORY__BV__LS__LS_VALUE_H

#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace ls {

/**
 * The value type used throughout the local search. All code goes through this
 * alias, so a faster representation can replace it later.
 */
using LsValue = cvc5::internal::BitVector;

}  // namespace ls
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__LS__LS_VALUE_H */
