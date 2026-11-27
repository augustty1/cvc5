; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-ops --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-ops --check-models --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-native-ops --check-models
; EXPECT: sat
; prop-c+ (FMCAD'20 Sec. V): bvxor, bvashr (the shifted value and the amount)
; and sign_extend as native local search operators. x >>a 2 = f9 makes x
; 111001xx, 80 >>a s = f0 needs s = 3, and sext(a, 4) = fa needs a = 1010.
; Without --bv-ls-const-bits the option has no effect (the base encodings).
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const s (_ BitVec 8))
(declare-const a (_ BitVec 4))
(assert (= (bvxor x y) #xa5))
(assert (= (bvashr x #x02) #xf9))
(assert (= (bvashr #x80 s) #xf0))
(assert (= ((_ sign_extend 4) a) #xfa))
(assert (bvult y #x60))
(check-sat)
