; COMMAND-LINE: --bv-ls
; EXPECT: sat
; bvsdiv and bvsrem are eliminated into ite terms, which term formula
; removal lifts into purification skolems with their own definitions.
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (= (bvsdiv x y) #xfffd))
(assert (= (bvsrem x y) #x0001))
(assert (bvslt y #x0000))
(check-sat)
