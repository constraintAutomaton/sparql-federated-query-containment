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

; We only have <sub_s> <sub_p> has relevant variables
; We check if there exist a way to make it so the query cannot produce results, regardless of the underlying database
(assert 
  (exists ((<e_sub_s> RDFValue) (<e_sub_p> RDFValue))
      (and
        (and
            (= <e_sub_s> <sub_s>)
            (= <e_sub_p> <sub_p>)
        )
        (not
          (and
            (P <sub_s> <sub_p> <sub_o> <default_graph>) 
            (P <sub_s2> <sub_p2> <sub_o2> <default_graph>) 
          )
        )
      )
      
  )
)
; ------------ Check-Sat ----------------------------
(check-sat)
