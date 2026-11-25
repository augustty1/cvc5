; COMMAND-LINE: --bv-ls --bv-ls-const-bits --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; With constant bits, local search keeps its DAG, its domains and its values
; across check-sat calls; x o 1 is odd in every call.
(set-logic QF_BV)
(declare-const x (_ BitVec 7))
(declare-const y (_ BitVec 8))
(assert (= (bvmul (concat x #b1) #x03) #x07))
(check-sat)
(push 1)
(assert (= (bvand (concat x #b1) #x01) #x00))
(check-sat)
(pop 1)
(assert (= y (bvadd (concat x #b1) #x01)))
(check-sat)
(push 1)
(assert (bvugt y #x80))
(check-sat)
