(set-logic ALL)
(declare-const x Int)

(declare-fun f (Int) Int)
(assert (= (f 0) (* 0 0)))
(assert (= (f 1) (* 1 1)))
(assert (= (f 2) (* 2 2)))
(assert (= (f 3) (* 3 3)))
(assert (= (f 4) (* 4 4)))
(assert (= (f 5) (* 5 5)))

(assert (or (<= 0 x 2) (<= 4 x 5)))
; (assert (or (<= 4 x 5) (<= 0 x 2)))
(assert (> (f x) 1000))
(check-sat)
