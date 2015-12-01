(set-logic QF_BV)
(set-info :smt-lib-version 2.0)

(declare-fun input0 () (_ BitVec 8))
(declare-fun input1 () (_ BitVec 8))
(declare-fun input2 () (_ BitVec 8))
(declare-fun input3 () (_ BitVec 8))
(declare-fun input4 () (_ BitVec 8))
(declare-fun input5 () (_ BitVec 8))
(declare-fun input6 () (_ BitVec 8))
(declare-fun input7 () (_ BitVec 8))

(define-fun next_c ((x (_ BitVec 8)) (c (_ BitVec 64))) (_ BitVec 64)
  (let ((y (bvsub (bvadd (bvor x #x21) (bvxor x #x21)))))
    (let ((y_ext ((_ sign_extend 56) y)))
      (bvsub (bvor y_ext c) (bvxor y_ext c))
      )
    )
  )

(assert (and (bvuge input0 #x21) (bvule input0 #x7e)))
(assert (and (bvuge input1 #x21) (bvule input1 #x7e)))
(assert (and (bvuge input2 #x21) (bvule input2 #x7e)))
(assert (and (bvuge input3 #x21) (bvule input3 #x7e)))
(assert (and (bvuge input4 #x21) (bvule input4 #x7e)))
(assert (and (bvuge input5 #x21) (bvule input5 #x7e)))
(assert (and (bvuge input6 #x21) (bvule input6 #x7e)))
(assert (and (bvuge input7 #x21) (bvule input7 #x7e)))

(declare-fun r0 () (_ BitVec 64))
(assert (= r0 #x614e5d7107432745))

(declare-fun c0 () (_ BitVec 64))
(assert (= c0 r0))

(declare-fun c1 () (_ BitVec 64))
(assert (= c1 (next_c input0 c0)))

;; (declare-fun c2 () (_ BitVec 64))
;; (assert (= c2 (next_c input1 c1)))

;; (declare-fun c3 () (_ BitVec 64))
;; (assert (= c3 (next_c input2 c2)))

;; (declare-fun c4 () (_ BitVec 64))
;; (assert (= c4 (next_c input3 c3)))

;; (declare-fun c5 () (_ BitVec 64))
;; (assert (= c5 (next_c input4 c4)))

;; (declare-fun c6 () (_ BitVec 64))
;; (assert (= c6 (next_c input5 c5)))

;; (declare-fun c7 () (_ BitVec 64))
;; (assert (= c7 (next_c input6 c6)))

;; (declare-fun c8 () (_ BitVec 64))
;; (assert (= c8 (next_c input7 c7)))

;; (declare-fun r1 () (_ BitVec 64))
;; (assert (= r1 #x122d4d05a4299633))

;; (declare-fun output_ext () (_ BitVec 64))
;; (assert
;;  (= output_ext
;;            (let ((cr (bvadd c8 r1)))
;;              (bvlshr (bvsub (bvadd (bvxor cr (bvashr cr #x000000000000003f))
;;                                    (bvlshr cr #x000000000000003f))
;;                             #x0000000000000001)
;;                      #x000000000000003f)
;;              ))
;;  )

;; (declare-fun output () (_ BitVec 32))
;; (assert
;;  (and (= output ((_ extract 31 0) output_ext)) (not (= output #x00000000)))
;;  )

(check-sat)
(get-model)
