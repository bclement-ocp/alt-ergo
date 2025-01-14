; Test lexicographic optimization
(set-option :produce-models true)
(set-logic ALL)
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (bvult x (_ bv2 32)))
(assert (bvule y (_ bv10 32)))
(maximize x)
(maximize y)
(check-sat)
(get-model)
(get-objectives)
