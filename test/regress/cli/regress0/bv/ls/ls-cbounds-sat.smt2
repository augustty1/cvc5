; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds --check-models --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-ineq-bounds --check-models
; EXPECT: sat
; prop-cb+ (FMCAD'20 Sec. V-A): the inverse values of an inequality are drawn
; within the bounds of the other satisfied inequalities on the same operand.
; The inequalities confine x to (0300, 0400) and y to [0380, x]; with
; x & 000f = 0005 and x + y = 0705 the only model is x = 0385, y = 0380.
; Without --bv-ls-const-bits the option has no effect.
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (bvult x #x0400))
(assert (bvugt x #x0300))
(assert (bvule y x))
(assert (bvuge y #x0380))
(assert (= (bvand x #x000f) #x0005))
(assert (= (bvadd x y) #x0705))
(check-sat)
