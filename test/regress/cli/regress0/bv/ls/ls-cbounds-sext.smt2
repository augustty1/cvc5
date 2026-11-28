; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-sext-ranges --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-ops --bv-ls-sext-ranges --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-native-ops --bv-ls-sext-ranges --bv-ls-ineq-bounds --check-models --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-sext-ranges --check-models
; EXPECT: sat
; prop-cb+ (FMCAD'20 Sec. V-A, ranges (3) and (4)): the inverse values of an
; inequality over a sign extension are drawn among the sign extensions, with
; the native SEXT and with the encoding of the adapter. a and b are 8-bit;
; 5 <= sext(a) < 60 and sext(b) <s -3 with a + b = 0x30.
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (bvuge ((_ sign_extend 24) a) #x00000005))
(assert (bvult ((_ sign_extend 24) a) #x00000060))
(assert (bvslt ((_ sign_extend 24) b) #xfffffffd))
(assert (= (bvadd a b) #x30))
(check-sat)
