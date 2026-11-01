; COMMAND-LINE: --bv-ls
; EXPECT: sat
; Factorization: local search runs out of propagation steps and
; bit-blasting answers.
(set-logic QF_BV)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const p Bool)
(assert (= (bvmul x y) #x0000008f))
(assert (bvult #x00000001 x))
(assert (bvult #x00000001 y))
(assert (or p (bvslt x #x00000000)))
(assert (= (bvashr x #x00000002) (bvlshr y #x00000001)))
(check-sat)
