import { describe, expect, it } from "vitest";
import { generateOvRv, generateThetaSmtLibString, generateSigmas, isContained, renameIriforSmt, SigmaTerm, tildeCheck, type IOv, type IRv, type Sigma, SEMANTIC } from '../lib/approaches/specs';
import { translate } from "sparqlalgebrajs";
import { instantiateTemplate } from '../lib/approaches/templates';
import { isError, result } from 'result-interface';

describe(renameIriforSmt.name, () => {
	it("should rename an iri", () => {
		const url = "https://webshop.defietsambassade.gent/fr/pechbijstand-tech-lane-ghent-campus-ardoyen";
		const expectedVariable = "webshop_defietsambassade_gent_fr_pechbijstand_tech_lane_ghent_campus_ardoyen";

		expect(renameIriforSmt(url)).toBe(expectedVariable);
	})
});

describe(generateOvRv.name, () => {
	it("should report the ov and rv variable given a query with projection", () => {
		const query = `
		PREFIX owl: <http://www.w3.org/2002/07/owl#>
		PREFIX rh: <http://rdf.rhea-db.org/>
		PREFIX up: <http://purl.uniprot.org/core/>
		
		SELECT ?swisslipid  ?organism {
		?swisslipid owl:equivalentClass ?chebi .
		?catalyticActivityAnnotation up:catalyticActivity ?rhea .
		?protein up:annotation ?catalyticActivityAnnotation ;
				up:organism ?organism .
		}
		`;
		const expectedRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" }
		];

		const expectedOv: IOv[] = [
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const { ov, rv } = generateOvRv(translate(query));

		expect(new Set(rv.map((el) => el.name))).toStrictEqual(new Set(expectedRv.map(el => el.name)));
		expect(new Set(ov.map((el) => el.name))).toStrictEqual(new Set(expectedOv.map(el => el.name)));
	});

	it("should report the ov and rv variable given a query with no projection", () => {
		const query = `
		PREFIX owl: <http://www.w3.org/2002/07/owl#>
		PREFIX rh: <http://rdf.rhea-db.org/>
		PREFIX up: <http://purl.uniprot.org/core/>
		
		SELECT * {
		?swisslipid owl:equivalentClass ?chebi .
		?catalyticActivityAnnotation up:catalyticActivity ?rhea .
		?protein up:annotation ?catalyticActivityAnnotation ;
				up:organism ?organism .
		}
		`;
		const expectedRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const expectedOv: IOv[] = [];

		const { ov, rv } = generateOvRv(translate(query));

		expect(new Set(rv.map((el) => el.name))).toStrictEqual(new Set(expectedRv.map(el => el.name)));
		expect(new Set(ov.map((el) => el.name))).toStrictEqual(new Set(expectedOv.map(el => el.name)));
	});
});

describe(generateSigmas.name, () => {
	describe("conjunctive queries with no filter", () => {
		it("should generate no sigma a query with no triple pattern", () => {
			const query = `SELECT * {}`;

			const expectedSigmas: Sigma[] = [];

			expect(generateSigmas(translate(query))).toStrictEqual(expectedSigmas);
		});

		it("should generate sigmas with a query with triple patterns", () => {
			const query = `
		PREFIX owl: <http://www.w3.org/2002/07/owl#>
		PREFIX rh: <http://rdf.rhea-db.org/>
		PREFIX up: <http://purl.uniprot.org/core/>
		
		SELECT * {
		?swisslipid owl:equivalentClass ?chebi .
		?catalyticActivityAnnotation up:catalyticActivity ?rhea .
		?protein up:annotation ?catalyticActivityAnnotation ;
		}`;

			const expectedSigmas: Sigma[] = [
				{
					subject: "<swisslipid>",
					predicate: "<w3_org_2002_07_owl_equivalentClass>",
					object: "<chebi>",

					iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
					literalDeclarations: [],
					variableDeclarations: [
						SigmaTerm.generateDeclareSmtLibString("<swisslipid>"),
						SigmaTerm.generateDeclareSmtLibString("<chebi>")
					]
				},
				{
					subject: "<catalyticActivityAnnotation>",
					predicate: "<purl_uniprot_org_core_catalyticActivity>",
					object: "<rhea>",

					iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_catalyticActivity>")],
					literalDeclarations: [],
					variableDeclarations: [
						SigmaTerm.generateDeclareSmtLibString("<catalyticActivityAnnotation>"),
						SigmaTerm.generateDeclareSmtLibString("<rhea>")
					]
				},
				{
					subject: "<protein>",
					predicate: "<purl_uniprot_org_core_annotation>",
					object: "<catalyticActivityAnnotation>",

					iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_annotation>")],
					literalDeclarations: [],
					variableDeclarations: [
						SigmaTerm.generateDeclareSmtLibString("<protein>"),
						SigmaTerm.generateDeclareSmtLibString("<catalyticActivityAnnotation>")
					]
				}
			];

			const resp = generateSigmas(translate(query));

			expect(resp.length).toBe(expectedSigmas.length);
			for (const [idx, sigma] of resp.entries()) {
				const expectedSigma = expectedSigmas[idx];

				expect(sigma.iriDeclarations).toStrictEqual(expectedSigma.iriDeclarations);
				expect(sigma.literalDeclarations).toStrictEqual(expectedSigma.literalDeclarations);
				expect(sigma.variableDeclarations).toStrictEqual(expectedSigma.variableDeclarations);

				expect(sigma.subject).toStrictEqual(expectedSigma.subject);
				expect(sigma.predicate).toStrictEqual(expectedSigma.predicate);
				expect(sigma.object).toStrictEqual(expectedSigma.object);
			}

		});
	});
});

describe(tildeCheck.name, () => {
	it("should return false if not the same number of variables is provided", () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
		];

		expect(tildeCheck(subRv, superRv)).toBe(false);
	});

	it("should return false if not the same variables are provided", () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi2" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea2" },
			{ name: "protein" }
		];

		expect(tildeCheck(subRv, superRv)).toBe(false);
	});

	it("should return true if the same variables are provided", () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		expect(tildeCheck(subRv, superRv)).toBe(true);
	});
});

describe(generateThetaSmtLibString.name, () => {
	it("should generate an empty SMT lib file given no sigma", () => {
		const sigmas: Sigma[] = [];
		const rv: IRv[] = [];

		const sigmaFormated = generateThetaSmtLibString(sigmas, rv);
		const expectedString = instantiateTemplate("", "", "", "");

		expect(sigmaFormated).toBe(expectedString);
	});

	it("should generate an SMT lib file given a sigma", () => {
		const sigma: Sigma =
		{
			subject: "<swisslipid>",
			predicate: "<w3_org_2002_07_owl_equivalentClass>",
			object: "<chebi>",

			iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
			literalDeclarations: [],
			variableDeclarations: [
				SigmaTerm.generateDeclareSmtLibString("<swisslipid>"),
				SigmaTerm.generateDeclareSmtLibString("<chebi>")
			]
		};

		const rv = [{ name: "swisslipid" }];

		const sigmaFormated = generateThetaSmtLibString([sigma], rv);

		const expectedString = `
; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <w3_org_2002_07_owl_equivalentClass> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <swisslipid> RDFValue)
(declare-const <chebi> RDFValue)
; ------------ Conjecture ---------------------------

(assert
	(and
		(or (P <swisslipid> <w3_org_2002_07_owl_equivalentClass> <chebi> <default_graph>))
	)
)


(assert
	(exists ((<e_swisslipid> RDFValue))
		(and
			(and
				(= <e_swisslipid> <swisslipid>)
			)
			(not
				(and
					(or (P <swisslipid> <w3_org_2002_07_owl_equivalentClass> <chebi> <default_graph>))
				)
			)
		)    
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)
`;

		expect(sigmaFormated).toBe(expectedString);
	});


	it("should generate an SMT lib file given a multiple sigmas", () => {
		const sigma1: Sigma = {
			subject: "<swisslipid>",
			predicate: "<w3_org_2002_07_owl_equivalentClass>",
			object: "<chebi>",

			iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
			literalDeclarations: [],
			variableDeclarations: [
				SigmaTerm.generateDeclareSmtLibString("<swisslipid>"),
				SigmaTerm.generateDeclareSmtLibString("<chebi>")
			]
		};

		const sigma2: Sigma = {
			subject: "<swisslipid_2>",
			predicate: "<l_foo>",
			object: "<chebi>",

			iriDeclarations: [],
			literalDeclarations: [SigmaTerm.generateDeclareSmtLibString("<l_foo>")],
			variableDeclarations: [
				SigmaTerm.generateDeclareSmtLibString("<swisslipid_2>"),
				SigmaTerm.generateDeclareSmtLibString("<chebi>")
			]
		};

		const sigma3: Sigma = {
			subject: "<swisslipid_3>",
			predicate: "<w3_org_2002_07_owl_equivalentClass_3>",
			object: "<chebi_3>",

			iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass_3>")],
			literalDeclarations: [],
			variableDeclarations: [
				SigmaTerm.generateDeclareSmtLibString("<swisslipid_3>"),
				SigmaTerm.generateDeclareSmtLibString("<chebi_3>")
			]
		};

		const expectedString = `
; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <w3_org_2002_07_owl_equivalentClass> RDFValue)
(declare-const <w3_org_2002_07_owl_equivalentClass_3> RDFValue)
; ------------ Literals -----------------------------
(declare-const <l_foo> RDFValue)
; ------------ Variables ----------------------------
(declare-const <swisslipid> RDFValue)
(declare-const <chebi> RDFValue)
(declare-const <swisslipid_2> RDFValue)
(declare-const <swisslipid_3> RDFValue)
(declare-const <chebi_3> RDFValue)
; ------------ Conjecture ---------------------------

(assert
	(and
		(or (P <swisslipid> <w3_org_2002_07_owl_equivalentClass> <chebi> <default_graph>))
		(or (P <swisslipid_2> <l_foo> <chebi> <default_graph>))
		(or (P <swisslipid_3> <w3_org_2002_07_owl_equivalentClass_3> <chebi_3> <default_graph>))
	)
)


(assert
	(exists ((<e_chebi_3> RDFValue) (<e_swisslipid_2> RDFValue))
		(and
			(and
				(= <e_chebi_3> <chebi_3>)
				(= <e_swisslipid_2> <swisslipid_2>)
			)
			(not
				(and
					(or (P <swisslipid> <w3_org_2002_07_owl_equivalentClass> <chebi> <default_graph>))
					(or (P <swisslipid_2> <l_foo> <chebi> <default_graph>))
					(or (P <swisslipid_3> <w3_org_2002_07_owl_equivalentClass_3> <chebi_3> <default_graph>))
				)
			)
		)    
	)
)
; ------------ Check-Sat ----------------------------
(check-sat)
`;

		const rv: IRv[] = [{ name: "chebi_3" }, { name: "swisslipid_2" }];

		const thetaFormat = generateThetaSmtLibString([sigma1, sigma2, sigma3], rv);
		expect(thetaFormat).toBe(expectedString);
	});


});

describe(tildeCheck.name, () => {
	it("should retun false given two relevant variable set that do not have the same size", () => {
		const rv1: IRv[] = [{ name: "foo1" }, { name: "foo2" }, { name: "foo3" }];
		const rv2: IRv[] = [{ name: "bar1" }, { name: "bar2" },];

		const resp = tildeCheck(rv1, rv2);

		expect(resp).toBe(false);
	});

	it("should retun false given two identical relevant variable sets", () => {
		const rv1: IRv[] = [{ name: "foo1" }, { name: "foo2" }, { name: "foo3" }];
		const rv2: IRv[] = [{ name: "bar1" }, { name: "bar2" }, { name: "bar3" }];

		const resp = tildeCheck(rv1, rv2);

		expect(resp).toBe(false);
	});

	it("should retun true given two relevant variable sets", () => {
		const rv1: IRv[] = [{ name: "foo1" }, { name: "foo2" }, { name: "foo3" }];
		const rv2: IRv[] = [{ name: "bar1" }, { name: "bar2" }, { name: "bar3" }];

		const resp = tildeCheck(rv1, rv2);

		expect(resp).toBe(false);
	});

	it("should retun true given two empty relevant variable sets", () => {
		const rv1: IRv[] = [];
		const rv2: IRv[] = [];

		const resp = tildeCheck(rv1, rv2);

		expect(resp).toBe(true);
	});
});

describe(isContained.name, () => {
	describe("set semantic", () => {
		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return true given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s <http://example.com#> ?o2.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it("should return true given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>. ?s ?p3 <http://example.com#>.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>.}");

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p <http://example.com#1>. ?s1 ?p2 ?o2.}");

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it("should return false given queries with multiple non identical projections", async () => {
			const subQ = translate("SELECT * WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT * WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it('should return false given an example contained query', async () => {
			const subQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE {
			?s ex:age ?age .
			}`);

			const superQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE  {
			?s ex:job ?job ;
				ex:age ?age .				
			}`);

			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it('should return false given an example contained query', async () => {
			const subQ = translate(`
				PREFIX ex: <http://example.org/>
	
				SELECT ?s ?age WHERE  {
				?s ex:job ?job ;
					ex:age ?age .				
				}`);


			const superQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE {
			?s ex:age ?age .
			}`);



			const resp = await isContained(subQ, superQ);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
		});
	});

	describe("bag-set semantic", () => {
		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
		});

		it("should return contain given a contained query", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?o ?p ?s.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses:{} }));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s <http://example.com#> ?o2.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>. ?s ?p3 <http://example.com#>.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>.}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p <http://example.com#1>. ?s1 ?p2 ?o2.}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple non identical projections", async () => {
			const subQ = translate("SELECT * WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT * WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it('should return false given an example contained query', async () => {

			const subQ = translate(`
				PREFIX ex: <http://example.org/>
	
				SELECT ?s ?age WHERE  {
				?s ex:job ?job ;
					ex:age ?age ;
					ex:email ?email.				
				}`);

			const superQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE {
			?s ex:age ?age .
			}`);

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});
	});

	describe("bag-set service clauses", () => {
		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE { SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({
				result: true,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {}
					}
				}
			}));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?o WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({
				result: false,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {}
					}
				}
			}));
		});

		it("should return true given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> {?s ?p ?o. ?s <http://example.com#> ?o2.}}");
			const superQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> {?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(resp).toStrictEqual(result({
				result: true,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {}
					}
				}
			}));
		});

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE { ?s ?p <http://example.com>. ?p <http://example.com> ?s. SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?s WHERE { ?s ?p <http://example.com>. SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, SEMANTIC.BAG_SET);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({
				result: true,
				smtlib: expect.any(String),
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {}
					}
				}
			}));
		});
	});
});