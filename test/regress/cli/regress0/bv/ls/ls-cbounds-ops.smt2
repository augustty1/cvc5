; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds --bv-ls-ineq-bounds-ops --check-models
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --bv-ls-ineq-bounds --bv-ls-ineq-bounds-ops --check-models --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-ineq-bounds-ops --check-models
; EXPECT: sat
; prop-cb+ beyond FMCAD'20 (as Bitwuzla): the inverse values of bvand and
; bvmul are also drawn within the bounds of the inequalities on the operand.
; x is in (0x20, 0x40), x & 0x0f = 0x05 and x * y = 0x0b5f.
(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (bvult x #x0040))
(assert (bvugt x #x0020))
(assert (= (bvand x #x000f) #x0005))
(assert (= (bvmul x y) #x0b5f))
(check-sat)
