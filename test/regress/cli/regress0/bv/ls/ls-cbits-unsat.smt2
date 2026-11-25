; COMMAND-LINE: --bv-ls --bv-ls-const-bits
; EXPECT: unsat
; An odd number never equals an even one: with constant bits the domain of
; the equality is the constant false (2x + 1 has domain xxxxxxx1, 2y has
; xxxxxxx0), so local search gives up on that root and bit-blasting answers.
(set-logic QF_BV)
(declare-const x (_ BitVec 7))
(declare-const y (_ BitVec 7))
(declare-const z (_ BitVec 8))
(assert (bvult z #x10))
(assert (= (bvadd (concat x #b0) (bvand z #x01) #x01) (concat y #b0)))
(assert (= (bvand z #x01) #x00))
(check-sat)
