; COMMAND-LINE: --bv-ls
; EXPECT: unsat
; Local search cannot show unsatisfiability; bit-blasting does.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvadd x y) #x07))
(assert (= (bvadd y x) #x08))
(check-sat)
