; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <w3_org_1999_02_22_rdf_syntax_ns_type> RDFValue)
(declare-const <example_org_GraduateStudent> RDFValue)
(declare-const <example_org_Department> RDFValue)
(declare-const <example_org_memberOf> RDFValue)
(declare-const <example_org_subOrganizationOf> RDFValue)
(declare-const <example_org_University1> RDFValue)
(declare-const <example_org_email> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <x> RDFValue)
(declare-const <y> RDFValue)
(declare-const <z> RDFValue)
; ------------ Conjecture ---------------------------
(assert
	(and
		(or (P <x> <w3_org_1999_02_22_rdf_syntax_ns_type> <example_org_GraduateStudent> <default_graph>))
		(or (P <y> <w3_org_1999_02_22_rdf_syntax_ns_type> <example_org_Department> <default_graph>))
		(or (P <x> <example_org_memberOf> <y> <default_graph>))
		(or (P <y> <example_org_subOrganizationOf> <example_org_University1> <default_graph>))
		(or (P <x> <example_org_email> <z> <default_graph>))
	)
)

(assert 
	(not 
		(exists ((<e_x> RDFValue) (<e_z> RDFValue))
			(and
				(or (P <x> <w3_org_1999_02_22_rdf_syntax_ns_type> <example_org_GraduateStudent> <default_graph>))
				(or (P <y> <w3_org_1999_02_22_rdf_syntax_ns_type> <example_org_Department> <default_graph>))
				(or (P <x> <example_org_memberOf> <y> <default_graph>))
				(or (P <y> <example_org_subOrganizationOf> <u> <default_graph>))
				(or (P <x> <example_org_email> <z> <default_graph>))
				(= <e_x> <x>)
				(= <e_z> <z>)
			)
		)
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)