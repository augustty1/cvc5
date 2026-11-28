; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds --seed=1
; EXPECT: unsat
; prop-cb+: inequalities without a common solution; the local search cannot
; answer unsat, so bit-blasting does.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x #x10))
(assert (bvugt x y))
(assert (bvugt y #x20))
(check-sat)
