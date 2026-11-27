; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-ops
; EXPECT: unsat
; prop-c+: targets that the native operators can never produce. A negative x
; shifted right stays negative, so x >>a 1 = 40 needs x >= 0, but x >= 80;
; and 7a is not a sign extension of a 4-bit value (its top 5 bits differ).
; Local search ends these moves in conflicts and bit-blasting answers unsat.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a (_ BitVec 4))
(declare-const b Bool)
(assert (bvuge x #x80))
(assert (or b (= (bvashr x #x01) #x40)))
(assert (or (not b) (= ((_ sign_extend 4) a) #x7a)))
(check-sat)
