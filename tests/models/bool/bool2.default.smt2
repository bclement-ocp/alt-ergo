(set-option :produce-models true)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-const x Bool)
(declare-const y Bool)
(assert (or x (! (not x) :named notx)))
(check-sat)
(get-model)
(get-assignment)