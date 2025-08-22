; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <example_org_job> RDFValue)
(declare-const <example_org_age> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <s> RDFValue)
(declare-const <job> RDFValue)
(declare-const <email> RDFValue)
(declare-const <age> RDFValue)
; ------------ Conjecture ---------------------------
(assert
	(and
		(or (P <s> <example_org_age> <age> <default_graph>))
		(or 
			(P <s> <example_org_job> <job> <default_graph>)
			(P <s> <example_org_job> <email> <default_graph>)
		)
	)
)

(assert 
	(not 
		(exists ((<e_s> RDFValue))
			(and
				(or (P <s> <example_org_job> <job> <default_graph>))
				(or (P <s> <example_org_age> <age> <default_graph>))
				(= <e_s> <s>)
			)
		)
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)