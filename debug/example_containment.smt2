; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ Variables ----------------------------
(declare-const <s> RDFValue)
(declare-const <p> RDFValue)
(declare-const <o> RDFValue)

(declare-const <s2> RDFValue)
(declare-const <p2> RDFValue)
(declare-const <o2> RDFValue)
(declare-const <o3> RDFValue)
; ------------ Conjecture ---------------------------

; Sub query
(assert 
  (and
    (P <s> <p> <o> <default_graph>) 
    (P <s2> <p2> <o2> <default_graph>) 
  )
)


; implication

(assert
    (forall ((<e_s> RDFValue) (<e_p> RDFValue))
        (and
            (and
                    (P <e_s> <e_p> <o> <default_graph>) 
                    (P <e_s> <e_p> <o3> <default_graph>) 
            )
            (= <e_s> <s>)
            (= <e_p> <p>)

        )
    )
)

; ------------ Check-Sat ----------------------------
(check-sat)
