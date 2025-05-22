; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ Variables ----------------------------
(declare-const <sub_s> RDFValue)
(declare-const <sub_p> RDFValue)
(declare-const <sub_o> RDFValue)

; ------------ Conjecture ---------------------------
(assert 
  (and
    (P <sub_s> <sub_p> <sub_o> <default_graph>) 
  )
)

(assert 
  (forall ((<e_sub_s> RDFValue) (<e_sub_p> RDFValue) (<e_sub_o> RDFValue) (<e_default_graph> RDFValue))  
    (not 
      (and 
        (and
          (P <e_sub_s> <e_sub_p> <e_sub_o> <e_default_graph>)
        )
        (and 
          (= <e_sub_s> <sub_s>)
          (= <e_sub_p> <sub_p>)
          (= <e_sub_o> <sub_o>)
          (= <e_default_graph> <default_graph>) 
        ) 
      )
    )
  )
)
; ------------ Check-Sat ----------------------------
(check-sat)
