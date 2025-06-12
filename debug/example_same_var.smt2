; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)

(declare-fun S (RDFValue) Bool)
(declare-fun P (RDFValue) Bool)
(declare-fun O (RDFValue) Bool)

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

; add s, p and o function to each of my operators

; == sub query ==
(assert 
  (and
    (distinct <sub_s> <sub_p> <sub_o> <sub_s2> <sub_p2> <sub_o2>)
    (P (S <sub_s>) (P <sub_p>) (O <sub_o>) <default_graph>) 
    (P <sub_s2> <sub_p2> <sub_o2> <default_graph>) 
  )
)

; == super query ==
(assert 
  (and
    (distinct <super_s> <super_p> <super_o> <super_s2> <super_p2> <super_o2>)
    (P <super_s> <super_p> <super_o> <default_graph>) 
    (P <super_s2> <super_p2> <super_o2> <default_graph>) 
  )
)

; let's suppose that the relevant variables are sub_s, sub_p and super_o and super_p
(assert
    (forall ((<e_sub_s> RDFValue) (<e_sub_p> RDFValue))
        (and 
            (and 
                (= <e_sub_s> <sub_s>)
                (= <e_sub_p> <sub_p>)
            )
            (and
                (or  (= <sub_s> <super_s>) (= <sub_s> <super_o>))
                (or  (= <sub_p> <super_s>) (= <sub_p> <super_p>))
            )
        )
    )
)


; ------------ Check-Sat ----------------------------
(check-sat)
; (get-model)
; (get-value (<sub_s> <sub_p> <super_s> <super_o>))
