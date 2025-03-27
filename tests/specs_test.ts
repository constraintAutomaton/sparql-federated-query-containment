import { describe, expect, it } from 'bun:test';
import { generateOvRv, generateSigmas, renameIriforSmt, SigmaTerm, tildeCheck, type IOv, type IRv, type Sigma } from '../lib/approaches/specs';
import { translate } from "sparqlalgebrajs";

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