import { describe, expect, it } from "vitest";
import { generateOvRv, generateSigmas, isContained, renameIriforSmt, SigmaTerm, tildeCheck, type IOv, type IRv, type Sigma, SEMANTIC, ISolverOption, tildeCheckBagSet, tildeCheckBag } from '../lib/specs';
import { translate } from "sparqlalgebrajs";
import { isError, result } from 'result-interface';
import * as Z3_SOLVER from "z3-solver";

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

					iriDeclarations: [{ term: "http://www.w3.org/2002/07/owl#equivalentClass", declaration: SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>") }],
					literalDeclarations: [],
					variableDeclarations: [
						{ term: "swisslipid", declaration: SigmaTerm.generateDeclareSmtLibString("<swisslipid>") },
						{ term: "chebi", declaration: SigmaTerm.generateDeclareSmtLibString("<chebi>") }
					],
					variables: ["swisslipid", "chebi"]
				},
				{
					subject: "<catalyticActivityAnnotation>",
					predicate: "<purl_uniprot_org_core_catalyticActivity>",
					object: "<rhea>",

					iriDeclarations: [{ term: "http://purl.uniprot.org/core/catalyticActivity", declaration: SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_catalyticActivity>") }],
					literalDeclarations: [],
					variableDeclarations: [
						{ term: "catalyticActivityAnnotation", declaration: SigmaTerm.generateDeclareSmtLibString("<catalyticActivityAnnotation>") },
						{ term: "rhea", declaration: SigmaTerm.generateDeclareSmtLibString("<rhea>") }
					],
					variables: ["catalyticActivityAnnotation", "rhea"]
				},
				{
					subject: "<protein>",
					predicate: "<purl_uniprot_org_core_annotation>",
					object: "<catalyticActivityAnnotation>",

					iriDeclarations: [{ term: "http://purl.uniprot.org/core/annotation", declaration: SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_annotation>") }],
					literalDeclarations: [],
					variableDeclarations: [
						{ term: "protein", declaration: SigmaTerm.generateDeclareSmtLibString("<protein>") },
						{ term: "catalyticActivityAnnotation", declaration: SigmaTerm.generateDeclareSmtLibString("<catalyticActivityAnnotation>") }
					],
					variables: ["protein", "catalyticActivityAnnotation"]
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

describe(tildeCheckBagSet.name, () => {
	it("should return false if not the same number of variables is provided", () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv
		};

		expect(tildeCheckBagSet(subQ, superQ)).toBe(false);
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

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi2" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea2" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv
		};

		expect(tildeCheckBagSet(subQ, superQ)).toBe(false);
	});

	it(`should return false given that ${tildeCheck.name} passed and the super query variables is not a super set of the sub query variables`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo"]),
			relevantVariables: superRv
		};

		expect(tildeCheckBagSet(subQ, superQ)).toBe(false);
	});

	it(`should return true given that ${tildeCheck.name} passed and the super query variables is a super set of the sub query variables`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv
		};

		expect(tildeCheckBagSet(subQ, superQ)).toBe(true);
	});
});

describe(tildeCheckBag.name, () => {

	it("should return false if not the same number of variables is provided", () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(false);
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

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi2" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea2" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(false);
	});

	it(`should return false given that ${tildeCheck.name} passed and the super query variables is not a super set of the sub query variables`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(false);
	});

	it(`should return false given that ${tildeCheckBagSet.name} passed and the number of sigmas in the super query is lower than the sub query`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(false);
	});

	it(`should return true given that ${tildeCheckBagSet.name} passed and the number of sigmas are equals`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(true);
	});

	it(`should return true given that ${tildeCheckBagSet.name} passed and the number of sigma of the super query is greater`, () => {
		const subRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const subQ = {
			variables: new Set([...subRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: subRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		}

		const superRv: IRv[] = [
			{ name: "swisslipid" },
			{ name: "organism" },
			{ name: "chebi" },
			{ name: "catalyticActivityAnnotation" },
			{ name: "rhea" },
			{ name: "protein" }
		];

		const superQ = {
			variables: new Set([...superRv.map((el) => el.name), "foo", "bar"]),
			relevantVariables: superRv,
			sigmas: [
				{
					subject: "a",
					predicate: "b",
					object: "c",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "d",
					predicate: "e",
					object: "f",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				},
				{
					subject: "g",
					predicate: "h",
					object: "i",

					iriDeclarations: [],
					literalDeclarations: [],
					variableDeclarations: [],

					variables: []
				}
			]
		};

		expect(tildeCheckBag(subQ, superQ)).toBe(true);
	});
});

describe(isContained.name, async () => {
	const Z3 = await Z3_SOLVER.init();

	describe("set semantic", () => {
		const option: ISolverOption = {
			semantic: SEMANTIC.SET,
			z3: Z3,
			sources: []
		};

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return true given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s <http://example.com#> ?o2.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return true given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>. ?s ?p3 <http://example.com#>.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>.}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p <http://example.com#1>. ?s1 ?p2 ?o2.}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return false given queries with multiple non identical projections", async () => {
			const subQ = translate("SELECT * WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT * WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

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

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
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



			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});
	});

	describe("bag-set semantic", () => {
		const option: ISolverOption = {
			semantic: SEMANTIC.BAG_SET,
			z3: Z3,
			sources: []
		};

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return contain given a contained query", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?o ?p ?s.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s <http://example.com#> ?o2.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>. ?s ?p3 <http://example.com#>.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s ?p2 <http://example.com#>.}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p <http://example.com#1>. ?s1 ?p2 ?o2.}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false given queries with multiple non identical projections", async () => {
			const subQ = translate("SELECT * WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT * WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

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

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});
	});

	describe("bag-set service clauses", () => {
		const option: ISolverOption = {
			semantic: SEMANTIC.BAG_SET,
			z3: Z3,
			sources: []
		};

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE { SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({
				result: true,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {},
						unionResponses: expect.any(Object)
					}
				},
			}));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?o WHERE {SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({
				result: false,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {},
						unionResponses: expect.any(Object)
					}
				}
			}));
		});

		it("should return true given a sub query with more triple patterns", async () => {
			const subQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> {?s ?p ?o. ?s <http://example.com#> ?o2.}}");
			const superQ = translate("SELECT ?s WHERE {SERVICE <http://example.com> {?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({
				result: true,
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {},
						unionResponses: expect.any(Object)
					}
				}
			}));
		});

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE { ?s ?p <http://example.com>. ?p <http://example.com> ?s. SERVICE <http://example.com> { ?s ?p ?o}}");
			const superQ = translate("SELECT ?s WHERE { ?s ?p <http://example.com>. SERVICE <http://example.com> { ?s ?p ?o}}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({
				result: true,
				smtlib: expect.any(String),
				nestedResponses: {
					"http://example.com": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {},
						unionResponses: expect.any(Object)
					}
				},
				unionResponses: expect.any(Object)
			}));
		});

		it("should return contain with an example query", async () => {
			const subQ = translate(`
				PREFIX rh: <http://rdf.rhea-db.org/>
				PREFIX up: <http://purl.uniprot.org/core/>

				SELECT ?uniprot ?mnemo ?rhea ?accession ?equation
				WHERE {
				SERVICE <https://sparql.uniprot.org/sparql> {
					#VALUES (?rhea) { (<http://rdf.rhea-db.org/11312>) (<http://rdf.rhea-db.org/11313>) }
					?uniprot up:reviewed true .
					?uniprot up:mnemonic ?mnemo .
					?uniprot up:organism ?taxid .
					?uniprot up:annotation/up:catalyticActivity/up:catalyzedReaction ?rhea . # where ?rhea comes from query upwards
					?taxid <http://purl.uniprot.org/core/strain> <http://purl.uniprot.org/taxonomy/10090#strain-752F89669B9A8D5A40A7219990C3010B>.
				}
				?rhea rh:accession ?accession .
				?rhea rh:equation ?equation .
				}
		`);
			const superQ = translate(`
				PREFIX rh: <http://rdf.rhea-db.org/>
				PREFIX up: <http://purl.uniprot.org/core/>

				SELECT ?uniprot ?mnemo ?rhea ?accession ?equation
				WHERE {
				SERVICE <https://sparql.uniprot.org/sparql> {
					#VALUES (?rhea) { (<http://rdf.rhea-db.org/11312>) (<http://rdf.rhea-db.org/11313>) }
					?uniprot up:reviewed true .
					?uniprot up:mnemonic ?mnemo .
					?uniprot up:organism ?taxid .
					?uniprot up:annotation/up:catalyticActivity/up:catalyzedReaction ?rhea . # where ?rhea comes from query upwards
				}
				?rhea rh:accession ?accession .
				?rhea rh:equation ?equation .
				}`);

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			
			expect(resp).toStrictEqual(result({
				result: true,
				smtlib: expect.any(String),
				unionResponses: expect.any(Object),
				nestedResponses: {
					"https://sparql.uniprot.org/sparql": {
						result: true,
						smtlib: expect.any(String),
						nestedResponses: {},
						unionResponses: expect.any(Object)
					}
				},
			}));
			
		});
	});

	describe("bag semantic", () => {

		const option: ISolverOption = {
			semantic: SEMANTIC.BAG,
			z3: Z3,
			sources: []
		};

		it("should return contain given 2 identical queries", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(isError(resp)).toBe(false);
			expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {}, unionResponses: expect.any(Object) }));
		});

		it("should return false a given without the same relevant variable that can be answer by a knowledge graph", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
			const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});

		it("should return false two queries not contained with set semantic", async () => {
			const subQ = translate("SELECT ?s WHERE {?s ?p ?o. ?s1 ?p2 ?o2. ?s3 ?p3 ?o3.}");
			const superQ = translate("SELECT ?s WHERE {?s ?p <http://example.com#1>. ?s1 ?p2 ?o2.}");

			const resp = await isContained(subQ, superQ, option);

			expect(resp).toStrictEqual(result({ result: false, smtlib: expect.any(String) }));
		});
	});
/**
	describe("union", () => {
		describe("set semantic", () => {
			const option: ISolverOption = {
				semantic: SEMANTIC.SET,
				z3: Z3,
				sources: []
			};

			it('should return true given a query with one union in the sub query', async () => {
				const subQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE {
			?s ex:age ?age .
			{
				?s ex:job ?job ;
			} UNION {
				?s ex:job ?email ;
			}
			}`);

				const superQ = translate(`
			PREFIX ex: <http://example.org/>

			SELECT ?s ?age WHERE  {
			?s ex:job ?job ;
				ex:age ?age .				
			}`);

				const resp = await isContained(subQ, superQ, option);

				expect(resp).toStrictEqual(result({ result: true, smtlib: expect.any(String), nestedResponses: {} }));
			});
		});

	});
*/
});