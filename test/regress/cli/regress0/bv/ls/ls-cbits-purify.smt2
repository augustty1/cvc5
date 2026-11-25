; COMMAND-LINE: --bv-ls --bv-ls-const-bits --seed=1
; COMMAND-LINE: --bv-ls --bv-ls-const-bits --seed=2
; EXPECT: sat
; With constant bits, the facts that use a purification skolem can fold to
; constants, so the node of the term it purifies is no longer reachable from
; the roots and the moves do not update it. Its model value must be
; evaluated from the leaves (plan D24); a stale value fails the self-check.
; (From regress0/bv/fuzz34.delta01.smtv1.smt2.)
(set-logic QF_BV)
(declare-const v0 (_ BitVec 4))
(assert (distinct #b0 (bvsub (bvor (bvcomp v0 #x0) (ite (bvslt #x0 ((_ sign_extend 3) (ite (bvslt ((_ zero_extend 3) (ite (distinct v0 #x0) #b1 #b0)) #x0) #b1 #b0))) #b1 #b0)) #b1)))
(check-sat)
