; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------

; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <sub_s> RDFValue)
(declare-const <sub_p> RDFValue)
(declare-const <sub_o> RDFValue)
; ------------ Conjecture ---------------------------

(assert
        (and
                (or (P <sub_s> <sub_p> <sub_o> <default_graph>))
        )
)


(assert
    (exists ((<e_sub_s> RDFValue))
        (and
            (and
                (= <e_sub_s> <sub_s>)
            )
            (not
                (and
                                        (or (P <sub_s> <sub_p> <sub_o> <default_graph>))
                )
            )
        )    
    )
)
; ------------ Check-Sat ----------------------------
(check-sat)

