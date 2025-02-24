import { describe, expect, it, test } from "bun:test";
import { translate } from 'sparqlalgebrajs';
import { hasPropertyPath, convertSPARQLIntoRelationalAlgebra, type IRelation, normalizeQueries, type INormalizeQueryResult } from '../lib/query';
import { isError, isResult, type Result } from "../lib/util";

describe('convertSPARQLIntoRelationalAlgebra', () => {
    it('should return an error given a query with a property path', () => {
        const query = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity|up:catalyticActivity2 ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`;
        const result = convertSPARQLIntoRelationalAlgebra(translate(query));
        expect(isError(result)).not.toBeUndefined();
    });

    it('should return the relation algebra of a SPARQL query', () => {
        const owlPrefix = 'http://www.w3.org/2002/07/owl#';
        const upPrefix = 'http://purl.uniprot.org/core/'

        const query = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`;

        const result = convertSPARQLIntoRelationalAlgebra(translate(query));
        expect(isError(result)).not.toBeUndefined();

        const expectedResult: IRelation[] = [
            {
                relation: `${owlPrefix}equivalentClass`,
                argument_s: "swisslipid",
                argument_o: "chebi"
            },
            {
                relation: `${upPrefix}catalyticActivity`,
                argument_s: "catalyticActivityAnnotation",
                argument_o: "rhea"
            },
            {
                relation: `${upPrefix}annotation`,
                argument_s: "protein",
                argument_o: "catalyticActivityAnnotation"
            },
            {
                relation: `${upPrefix}organism`,
                argument_s: "protein",
                argument_o: "organism"
            },
        ];

        expect(isResult(result) ? result.result : result.error).toStrictEqual(expectedResult);
    });
});

describe('hasPropertyPath', () => {
    it('should return false given a query with no property path', () => {
        const query = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`;
        expect(hasPropertyPath(translate(query))).toBeFalse();
    });

    it('should return true given a query with a property path', () => {
        const query = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity|up:catalyticActivity2 ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`;
        expect(hasPropertyPath(translate(query))).toBeTrue();
    });

    it('should return true given a query with multiple property paths', () => {
        const query = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        SERVICE <https://sparql.rhea-db.org/sparql> {
            ?rhea rh:side/rh:contains/rh:compound ?compound .
            ?compound (rh:chebi|(rh:reactivePart/rh:chebi)|(rh:underlyingChebi/rh:chebi)) ?metabolite .
            ?compound2 (rh:chebi|(rh:reactivePart/rh:chebi)|(rh:underlyingChebi/rh:chebi)) ?metabolite .
        }
        SERVICE <https://sparql.uniprot.org/sparql> {
            ?catalyticActivityAnnotation up:catalyticActivity/up:catalyzedReaction ?rhea .
            ?protein up:annotation ?catalyticActivityAnnotation ;
                    up:organism ?organism .
        }
        }`;
        expect(hasPropertyPath(translate(query))).toBeTrue();
    });
});

describe("normalizeQueries", () => {
    it("should have the same queries given 2 identical queries", () => {
        const queryString = `
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`;
        const query1 = translate(queryString);
        const query2 = translate(queryString);
        const resp = <Result<INormalizeQueryResult, Error>>normalizeQueries(query1, query2);
        expect(isResult(resp)).toBe(true);
        const { result } = <{ result: INormalizeQueryResult }>resp
        expect(result.mapping).toStrictEqual(new Map([
            ["swisslipid", "swisslipid"],
            ["organism", "organism"],
            ["chebi", "chebi"],
            ["catalyticActivityAnnotation", "catalyticActivityAnnotation"],
            ["rhea", "rhea"],
            ["protein", "protein"]
        ]));

        expect(result.queries.query_1).toStrictEqual(query1);
        expect(result.queries.query_2).toStrictEqual(query2);
    });

    it("should rewrite the query given 2 identical queries with different variable names", () => {
    
        const query1 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`);
        const query2 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid1  ?organism1 {
        ?swisslipid1 owl:equivalentClass ?chebi1 .
        ?catalyticActivityAnnotation1 up:catalyticActivity ?rhea1 .
        ?protein1 up:annotation ?catalyticActivityAnnotation1 ;
                up:organism ?organism1 .
        }`);
        const resp = <Result<INormalizeQueryResult, Error>>normalizeQueries(query1, query2);
        expect(isResult(resp)).toBe(true);
        const { result } = <{ result: INormalizeQueryResult }>resp
        expect(result.mapping).toStrictEqual(new Map([
            ["swisslipid1", "swisslipid"],
            ["organism1", "organism"],
            ["chebi1", "chebi"],
            ["catalyticActivityAnnotation1", "catalyticActivityAnnotation"],
            ["rhea1", "rhea"],
            ["protein1", "protein"]
        ]));

        expect(result.queries.query_1).toStrictEqual(query1);
        expect(result.queries.query_2).toStrictEqual(query1);
    });

    it("should rewrite a query with less variables", () => {
    
        const query1 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`);
        const query2 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT * WHERE {
        ?swisslipid1 owl:equivalentClass ?chebi1 .
        ?catalyticActivityAnnotation1 up:catalyticActivity ?rhea1 .
        }`);
        const resp = <Result<INormalizeQueryResult, Error>>normalizeQueries(query1, query2);
        expect(isResult(resp)).toBe(true);
        const { result } = <{ result: INormalizeQueryResult }>resp
        expect(result.mapping).toStrictEqual(new Map([
            ["swisslipid1", "swisslipid"],
            ["chebi1", "chebi"],
            ["catalyticActivityAnnotation1", "catalyticActivityAnnotation"],
            ["rhea1", "rhea"],
        ]));

        const expectedQuery = translate(`
            PREFIX owl: <http://www.w3.org/2002/07/owl#>
            PREFIX rh: <http://rdf.rhea-db.org/>
            PREFIX up: <http://purl.uniprot.org/core/>
            SELECT * WHERE {
            ?swisslipid owl:equivalentClass ?chebi .
            ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
            }`)
        expect(result.queries.query_1).toStrictEqual(query1);
        expect(result.queries.query_2).toStrictEqual(expectedQuery);
    });

    it("should not rewrite queries that have nothing in common", () => {
    
        const query1 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`);
        const query2 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl2#>
        PREFIX rh: <http://rdf.rhea-db.org2/>
        PREFIX up: <http://purl.uniprot.org/core2/>
        SELECT * WHERE {
        ?s owl:equivalentClass2 ?o
        }`);
        const resp = <Result<INormalizeQueryResult, Error>>normalizeQueries(query1, query2);
        expect(isResult(resp)).toBe(true);
        const { result } = <{ result: INormalizeQueryResult }>resp
        expect(result.mapping).toStrictEqual(new Map([]));

        expect(result.queries.query_1).toStrictEqual(query1);
        expect(result.queries.query_2).toStrictEqual(query2);
    });

    it("should rewrite the query given it has different variables that cannot be rewritten", () => {
    
        const query1 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid  ?organism {
        ?swisslipid owl:equivalentClass ?chebi .
        ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
        ?protein up:annotation ?catalyticActivityAnnotation ;
                up:organism ?organism .
        }`);
        const query2 = translate(`
        PREFIX owl: <http://www.w3.org/2002/07/owl#>
        PREFIX rh: <http://rdf.rhea-db.org/>
        PREFIX up: <http://purl.uniprot.org/core/>
        SELECT ?swisslipid1  ?organism1 {
        ?swisslipid1 owl:equivalentClass ?chebi1 .
        ?catalyticActivityAnnotation1 up:catalyticActivity ?rhea1 .
        ?protein1 up:annotation ?catalyticActivityAnnotation1 ;
                up:organism ?organism1 ;
                owl:equivalentClass ?v0 ;
                <http://www.example.com#foo> ?v1 .
        ?v2 <http://www.example.com#foo2>  ?v3 .
        }`);
        const resp = <Result<INormalizeQueryResult, Error>>normalizeQueries(query1, query2);
        expect(isResult(resp)).toBe(true);
        const { result } = <{ result: INormalizeQueryResult }>resp
        expect(result.mapping).toStrictEqual(new Map([
            ["swisslipid1", "swisslipid"],
            ["organism1", "organism"],
            ["chebi1", "chebi"],
            ["catalyticActivityAnnotation1", "catalyticActivityAnnotation"],
            ["rhea1", "rhea"],
            ["protein1", "protein"]
        ]));

        const expectedQuery = translate(`
            PREFIX owl: <http://www.w3.org/2002/07/owl#>
            PREFIX rh: <http://rdf.rhea-db.org/>
            PREFIX up: <http://purl.uniprot.org/core/>
            SELECT ?swisslipid  ?organism {
            ?swisslipid owl:equivalentClass ?chebi .
            ?catalyticActivityAnnotation up:catalyticActivity ?rhea .
            ?protein up:annotation ?catalyticActivityAnnotation ;
                    up:organism ?organism ;
                    owl:equivalentClass ?v0 ;
                    <http://www.example.com#foo> ?v1 .
            ?v2 <http://www.example.com#foo2>  ?v3 .
            }`)
        expect(result.queries.query_1).toStrictEqual(query1);
        expect(result.queries.query_2).toStrictEqual(expectedQuery);
    });
});