; COMMAND-LINE: --bv-ls
; EXPECT: sat
; Solved by local search alone: inverse values for bvmul, bvadd and
; zero_extend, and an ite over Boolean structure.
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(declare-const z (_ BitVec 16))
(declare-const p Bool)
(assert (= (bvmul x #x0000000000042f01) #xffffffff00000001))
(assert (= (bvadd y x) ((_ zero_extend 48) z)))
(assert (ite p (bvslt ((_ sign_extend 48) z) #x0000000000000000) (= ((_ extract 3 0) z) #xa)))
(assert (distinct x y))
(assert (bvuge (bvudiv y #x0000000000000003) #x0000000000000002))
(check-sat)
