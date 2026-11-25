; COMMAND-LINE: --bv-ls --bv-ls-const-bits
; EXPECT: sat
; Constant bits (prop-c, FMCAD'20): a mask, a shift by a variable amount, a
; product with an operand whose low byte is zero, a quotient by a divisor of
; at least 4 and a remainder by a power of two. The domains fix bits of these
; terms and the search chooses values modulo them.
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(declare-const s (_ BitVec 4))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= (bvand x #xff00) #x1200))
(assert (= (bvshl y ((_ zero_extend 12) s)) #x0a40))
(assert (= (bvmul (concat a #x00) (concat #x00 b)) #x3c00))
(assert (bvult (bvudiv x (bvor ((_ zero_extend 8) b) #x0004)) #x0800))
(assert (= (bvurem y #x0010) #x0000))
(assert (distinct a b))
(check-sat)
