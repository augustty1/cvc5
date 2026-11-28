; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-slt --bv-ls-ineq-bounds --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-slt --bv-ls-ineq-bounds --check-models --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-slt --check-models
; COMMAND-LINE: --bv-ls --bv-ls-native-slt --check-models
; EXPECT: sat
; prop-cb+: the signed inequalities as the native SLT, with signed bounds.
; They confine x to (-16, 16) and y to (-4, x); x * 3 = y + 9 then leaves
; x = 3 and y = 0, x = 4 and y = 3, ... Without --bv-ls-const-bits the
; option has no effect.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvslt #xf0 x))
(assert (bvslt x #x10))
(assert (bvslt y x))
(assert (bvsgt y #xfc))
(assert (= (bvmul x #x03) (bvadd y #x09)))
(check-sat)
