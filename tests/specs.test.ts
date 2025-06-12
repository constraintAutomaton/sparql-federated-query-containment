import { describe, expect, it } from "vitest";
import { generateOvRv, generateThetaSmtLibString, generateSigmas, isContained, renameIriforSmt, SigmaTerm, tildeCheck, type IOv, type IRv, type Sigma } from '../lib/approaches/specs';
import { translate } from "sparqlalgebrajs";
import { instantiatePhiTemplate, instantiateTemplatePhiConjecture, instantiateTriplePatternStatementTemplate } from '../lib/approaches/templates';
import { isError, type IError } from 'result-interface';

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

            expect(generateSigmas(translate(query), "sub")).toStrictEqual(expectedSigmas);
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
                    subject: "<sub_swisslipid>",
                    predicate: "<w3_org_2002_07_owl_equivalentClass>",
                    object: "<sub_chebi>",

                    iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
                    literalDeclarations: [],
                    variableDeclarations: [
                        SigmaTerm.generateDeclareSmtLibString("<sub_swisslipid>"),
                        SigmaTerm.generateDeclareSmtLibString("<sub_chebi>")
                    ]
                },
                {
                    subject: "<sub_catalyticActivityAnnotation>",
                    predicate: "<purl_uniprot_org_core_catalyticActivity>",
                    object: "<sub_rhea>",

                    iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_catalyticActivity>")],
                    literalDeclarations: [],
                    variableDeclarations: [
                        SigmaTerm.generateDeclareSmtLibString("<sub_catalyticActivityAnnotation>"),
                        SigmaTerm.generateDeclareSmtLibString("<sub_rhea>")
                    ]
                },
                {
                    subject: "<sub_protein>",
                    predicate: "<purl_uniprot_org_core_annotation>",
                    object: "<sub_catalyticActivityAnnotation>",

                    iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<purl_uniprot_org_core_annotation>")],
                    literalDeclarations: [],
                    variableDeclarations: [
                        SigmaTerm.generateDeclareSmtLibString("<sub_protein>"),
                        SigmaTerm.generateDeclareSmtLibString("<sub_catalyticActivityAnnotation>")
                    ]
                }
            ];

            const resp = generateSigmas(translate(query), "sub");

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
        const expectedString = instantiatePhiTemplate("", "", "", "");

        expect(sigmaFormated).toBe(expectedString);
    });

    it("should generate an SMT lib file given a sigma", () => {
        const sigma: Sigma =
        {
            subject: "<sub_swisslipid>",
            predicate: "<w3_org_2002_07_owl_equivalentClass>",
            object: "<sub_chebi>",

            iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
            literalDeclarations: [],
            variableDeclarations: [
                SigmaTerm.generateDeclareSmtLibString("<sub_swisslipid>"),
                SigmaTerm.generateDeclareSmtLibString("<sub_chebi>")
            ]
        };

        const rv = [{name:"sub_swisslipid"}];

        const sigmaFormated = generateThetaSmtLibString([sigma], rv);
        
        const expectedString =`
; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
(declare-const <w3_org_2002_07_owl_equivalentClass> RDFValue)
; ------------ Literals -----------------------------

; ------------ Variables ----------------------------
(declare-const <sub_swisslipid> RDFValue)
(declare-const <sub_chebi> RDFValue)
; ------------ Conjecture ---------------------------

(assert
    (and
		(or (P <sub_swisslipid> <w3_org_2002_07_owl_equivalentClass> <sub_chebi> <default_graph>))
    )
)


(assert
    (exists ((<e_sub_swisslipid> RDFValue))
        (and
            (and
				(= <e_sub_swisslipid> <sub_swisslipid>)
            )
            (not
                (and
					(or (P <sub_swisslipid> <w3_org_2002_07_owl_equivalentClass> <sub_chebi> <default_graph>))
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
            subject: "<sub_swisslipid>",
            predicate: "<w3_org_2002_07_owl_equivalentClass>",
            object: "<sub_chebi>",

            iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass>")],
            literalDeclarations: [],
            variableDeclarations: [
                SigmaTerm.generateDeclareSmtLibString("<sub_swisslipid>"),
                SigmaTerm.generateDeclareSmtLibString("<sub_chebi>")
            ]
        };

        const sigma2: Sigma = {
            subject: "<sub_swisslipid_2>",
            predicate: "<l_foo>",
            object: "<sub_chebi>",

            iriDeclarations: [],
            literalDeclarations: [SigmaTerm.generateDeclareSmtLibString("<l_foo>")],
            variableDeclarations: [
                SigmaTerm.generateDeclareSmtLibString("<sub_swisslipid_2>"),
                SigmaTerm.generateDeclareSmtLibString("<sub_chebi>")
            ]
        };

        const sigma3: Sigma = {
            subject: "<sub_swisslipid_3>",
            predicate: "<w3_org_2002_07_owl_equivalentClass_3>",
            object: "<sub_chebi_3>",

            iriDeclarations: [SigmaTerm.generateDeclareSmtLibString("<w3_org_2002_07_owl_equivalentClass_3>")],
            literalDeclarations: [],
            variableDeclarations: [
                SigmaTerm.generateDeclareSmtLibString("<sub_swisslipid_3>"),
                SigmaTerm.generateDeclareSmtLibString("<sub_chebi_3>")
            ]
        };

        const expectedString =`
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
(declare-const <sub_swisslipid> RDFValue)
(declare-const <sub_chebi> RDFValue)
(declare-const <sub_swisslipid_2> RDFValue)
(declare-const <sub_swisslipid_3> RDFValue)
(declare-const <sub_chebi_3> RDFValue)
; ------------ Conjecture ---------------------------

(assert
	(and
		(or (P <sub_swisslipid> <w3_org_2002_07_owl_equivalentClass> <sub_chebi> <default_graph>))
		(or (P <sub_swisslipid_2> <l_foo> <sub_chebi> <default_graph>))
		(or (P <sub_swisslipid_3> <w3_org_2002_07_owl_equivalentClass_3> <sub_chebi_3> <default_graph>))
	)
)


(assert
    (exists ((<e_sub_chebi_3> RDFValue) (<e_sub_swisslipid_2> RDFValue))
        (and
            (and
				(= <e_sub_chebi_3> <sub_chebi_3>)
				(= <e_sub_swisslipid_2> <sub_swisslipid_2>)
            )
            (not
                (and
					(or (P <sub_swisslipid> <w3_org_2002_07_owl_equivalentClass> <sub_chebi> <default_graph>))
					(or (P <sub_swisslipid_2> <l_foo> <sub_chebi> <default_graph>))
					(or (P <sub_swisslipid_3> <w3_org_2002_07_owl_equivalentClass_3> <sub_chebi_3> <default_graph>))
                )
            )
        )    
    )
)
; ------------ Check-Sat ----------------------------
(check-sat)
`;
		
		const rv: IRv[] = [{name: "sub_chebi_3"}, {name:"sub_swisslipid_2"}];

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
    it("should return an error given a two queries with the same relevant variables", async () => {
        const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
        const superQ = translate("SELECT ?s WHERE {?s ?p ?o}");

        const resp = await isContained(subQ, superQ);

        expect(isError(resp)).toBe(true);
        expect((<any>resp).error).toBe("not implemented");
    });

    it("should return false given queries the queries does not have the same relevant variables and the sub query can produce results", async () => {
        const subQ = translate("SELECT ?s WHERE {?s ?p ?o}");
        const superQ = translate("SELECT ?o WHERE {?s ?p ?o}");

        const resp = await isContained(subQ, superQ);

        expect(isError(resp)).toBe(true);
        expect((<any>resp).error).toBe("not implemented");
    });
});