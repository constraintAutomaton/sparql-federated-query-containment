; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <example_org_age> RDFValue)
(declare-const <example_org_job> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <s> RDFValue)
(declare-const <age> RDFValue)
(declare-const <job> RDFValue)
; ------------ Conjecture ---------------------------
(assert
	(and
		(or (P <s> <example_org_age> <age> <default_graph>))
	)
)

(assert 
	(not 
		(exists ((<e_s> RDFValue) (<e_age> RDFValue))
			(and
				(or (P <s> <example_org_job> <job> <default_graph>))
				(or (P <s> <example_org_age> <age> <default_graph>))
				(= <e_s> <s>)
				(= <e_age> <age>)
			)
		)
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)