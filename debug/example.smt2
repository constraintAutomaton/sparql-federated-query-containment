; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <example_com_> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <s> RDFValue)
(declare-const <p> RDFValue)
(declare-const <o> RDFValue)
(declare-const <o2> RDFValue)
; ------------ Conjecture ---------------------------

(assert
	(and
		(or (P <s> <p> <o> <default_graph>))
		(or (P <s> <example_com_> <o2> <default_graph>))
	)
)


(assert
	(exists ((<e_s> RDFValue) (<e_p> RDFValue) (<e_o> RDFValue) (<e_o2> RDFValue))
		(and
			(and
				(= <e_s> <s>)
				(= <e_p> <p>)
				(= <e_o> <o>)
				(= <e_o2> <o2>)
			)
			(not
				(and
					(or (P <s> <p> <o> <default_graph>))
					(or (P <s> <example_com_> <o2> <default_graph>))
				)
			)
		)    
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)