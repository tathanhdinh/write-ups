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

(define-fun or_with_x21_then_double ((x (_ BitVec 8))) (_ BitVec 32)
  (let ((x_ext ((_ zero_extend 24) x)))
    (let ((x_ext_or_x21 (bvor x_ext #x00000021)))
      (bvadd x_ext_or_x21 x_ext_or_x21)
      )
    )
  )

(define-fun xor_with_x21 ((x (_ BitVec 8))) (_ BitVec 32)
  (let ((x_ext ((_ zero_extend 24) x)))
    (bvxor x_ext #x00000021)
    )
  )

(define-fun next_c ((x (_ BitVec 8)) (c (_ BitVec 64)) (h (_ BitVec 64))) (_ BitVec 64)
  (let ((local0 (bvsub (or_with_x21_then_double x) (xor_with_x21 x))))
    (let((local1 ((_ zero_extend 32) local0)))
      (let ((local2 (bvshl local1 h)))
          (let ((local3 (bvor local2 c)) (local4 (bvxor local2 c)))
            (bvsub (bvadd local3 local3) local4)
            )
          )
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

;; calculate checksum from input
(declare-fun r0 () (_ BitVec 64))
(assert (= r0 #x614e5d7107432745))

(declare-fun c0 () (_ BitVec 64))
(assert (= c0 r0))

(declare-fun c1 () (_ BitVec 64))
(assert (= c1 (next_c input0 c0 #x0000000000000000)))

(declare-fun c2 () (_ BitVec 64))
(assert (= c2 (next_c input1 c1 #x0000000000000008)))

(declare-fun c3 () (_ BitVec 64))
(assert (= c3 (next_c input2 c2 #x0000000000000010)))

(declare-fun c4 () (_ BitVec 64))
(assert (= c4 (next_c input3 c3 #x0000000000000018)))

(declare-fun c5 () (_ BitVec 64))
(assert (= c5 (next_c input4 c4 #x0000000000000020)))

(declare-fun c6 () (_ BitVec 64))
(assert (= c6 (next_c input5 c5 #x0000000000000028)))

(declare-fun c7 () (_ BitVec 64))
(assert (= c7 (next_c input6 c6 #x0000000000000030)))

(declare-fun c8 () (_ BitVec 64))
(assert (= c8 (next_c input7 c7 #x0000000000000038)))

(declare-fun r1 () (_ BitVec 64))
(assert (= r1 #x122d4d05a4299633))

;; verify checksum
(declare-fun output_ext () (_ BitVec 64))
(assert (= output_ext
           (let ((cr (bvadd c8 r1)))
             (bvlshr (bvsub (bvadd (bvxor cr (bvashr cr #x000000000000003f))
                                   (bvlshr cr #x000000000000003f))
                            #x0000000000000001)
                     #x000000000000003f)
             )
           )
        )

(declare-fun output () (_ BitVec 32))
(assert (and (= output ((_ extract 31 0) output_ext)) (not (= output #x00000000)))
 )

(check-sat)
(get-value (input0 input1 input2 input3 input4 input5 input6 input7))
