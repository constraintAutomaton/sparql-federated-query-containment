; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ Variables ----------------------------
(declare-const <sub_s> RDFValue)
(declare-const <sub_p> RDFValue)
(declare-const <sub_o> RDFValue)

(declare-const <sub_s2> RDFValue)
(declare-const <sub_p2> RDFValue)
(declare-const <sub_o2> RDFValue)

(declare-const <super_s> RDFValue)
(declare-const <super_p> RDFValue)
(declare-const <super_o> RDFValue)

(declare-const <super_s2> RDFValue)
(declare-const <super_p2> RDFValue)
(declare-const <super_o2> RDFValue)
; ------------ Conjecture ---------------------------
; == sub query ==
(assert 
  (and
    (P <sub_s> <sub_p> <sub_o> <default_graph>) 
    (P <sub_s2> <sub_p2> <sub_o2> <default_graph>) 
  )
)

; == super query ==
(assert 
  (and
    (P <super_s> <super_p> <super_o> <default_graph>) 
    (P <super_s2> <super_p2> <super_o2> <default_graph>) 
  )
)
(forall ()
  
  (and
    (or (= <sub_s> <super_s>) (= <sub_s> <super_s2>) (= <sub_s> <super_p>) (= <sub_s> <super_o>) (= <sub_s> <super_o2>))
    (or (= <sub_s2> <super_s>) (= <sub_s2> <super_s2>) (= <sub_s2> <super_p>) (= <sub_s2> <super_o>) (= <sub_s2> <super_o2>))
    (or (= <sub_p> <super_s>) (= <sub_p> <super_s2>) (= <sub_p> <super_p>) (= <sub_p> <super_o>) (= <sub_p> <super_o2>))
    (or (= <sub_p2> <super_s>) (= <sub_p2> <super_s2>) (= <sub_p2> <super_p>) (= <sub_p2> <super_o>) (= <sub_p2> <super_o2>))
    (or (= <sub_o> <super_s>) (= <sub_o> <super_s2>) (= <sub_o> <super_p>) (= <sub_o> <super_o>) (= <sub_o> <super_o2>))
    (or (= <sub_o2> <super_s>) (= <sub_o2> <super_s2>) (= <sub_o2> <super_p>) (= <sub_o2> <super_o>) (= <sub_o2> <super_o2>))
  )
)
(assert
  (and
    (or (= <sub_s> <super_s>) (= <sub_s> <super_s2>) (= <sub_s> <super_p>) (= <sub_s> <super_o>) (= <sub_s> <super_o2>))
    (or (= <sub_s2> <super_s>) (= <sub_s2> <super_s2>) (= <sub_s2> <super_p>) (= <sub_s2> <super_o>) (= <sub_s2> <super_o2>))
    (or (= <sub_p> <super_s>) (= <sub_p> <super_s2>) (= <sub_p> <super_p>) (= <sub_p> <super_o>) (= <sub_p> <super_o2>))
    (or (= <sub_p2> <super_s>) (= <sub_p2> <super_s2>) (= <sub_p2> <super_p>) (= <sub_p2> <super_o>) (= <sub_p2> <super_o2>))
    (or (= <sub_o> <super_s>) (= <sub_o> <super_s2>) (= <sub_o> <super_p>) (= <sub_o> <super_o>) (= <sub_o> <super_o2>))
    (or (= <sub_o2> <super_s>) (= <sub_o2> <super_s2>) (= <sub_o2> <super_p>) (= <sub_o2> <super_o>) (= <sub_o2> <super_o2>))
  )
)

; ------------ Check-Sat ----------------------------
(check-sat)