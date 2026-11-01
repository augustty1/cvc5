; COMMAND-LINE: --bv-ls --incremental
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; Local search keeps its DAG and values across check-sat calls.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvmul x #x03) #x07))
(check-sat)
(push 1)
(assert (= x #x00))
(check-sat)
(pop 1)
(assert (= y (bvadd x #x01)))
(check-sat)
(push 1)
(assert (bvugt y #x80))
(check-sat)
(pop 1)
