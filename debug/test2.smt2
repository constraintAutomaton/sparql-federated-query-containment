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
; ------------ Conjecture ---------------------------
(assert 
  (and
    (P <sub_s> <sub_p> <sub_o> <default_graph>) 
    (P <sub_s2> <sub_p2> <sub_o2> <default_graph>) 
  )
)

(assert 
  (forall ((<e_sub_s> RDFValue) (<e_sub_p> RDFValue) (<e_sub_o> RDFValue) (<e_sub_s2> RDFValue) (<e_sub_p2> RDFValue) (<e_sub_o2> RDFValue) (<e_default_graph> RDFValue))  
    (not 
      (and 
        (and
          (P <sub_s> <sub_p> <sub_o> <default_graph>) 
          (P <sub_s2> <sub_p2> <sub_o2> <default_graph>) 
        )
        (and 
          (= <e_sub_s> <sub_s>)
          (= <e_sub_p> <sub_p>)
          (= <e_sub_o> <sub_o>)
          
          (= <e_sub_s2> <sub_s2>)
          (= <e_sub_p2> <sub_p2>)
          (= <e_sub_o2> <sub_o2>)

          (= <e_default_graph> <default_graph>) 
        ) 
      )
    )
  )
)
; ------------ Check-Sat ----------------------------
(check-sat)
