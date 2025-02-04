import { describe, expect, it, test } from "bun:test";
import { translate } from 'sparqlalgebrajs';
import { hasPropertyPath, convertSPARQLIntoRelationalAlgebra, type IRelation } from '../query';
import { isError, isResult } from "../util";

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