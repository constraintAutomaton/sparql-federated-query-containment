import { Algebra, Util } from 'sparqlalgebrajs';
import { type Result, RDF_FACTORY } from './util';
import { isomorphic } from "rdf-isomorphic";

const PATTERN_TERMS_NAME: (keyof Algebra.Pattern)[] = ["subject", "predicate", "object", "graph"];
/**
 * create a query by deleted a triple patterns with predicates not in the source predicate list
 * @param {Algebra.Operation} query - Query to filtered
 * @param {string[]} sourcePredicates - List of predicate present in the source
 * @returns {Algebra.Operation} Relevant subquery
 */
export function createRelevantSubQuery(query: Algebra.Operation, sourcePredicates: Set<string>): Algebra.Operation {
    const operationModifier = {
        [Algebra.types.BGP]: (op: Algebra.Bgp) => {
            const patternResulting = [];
            for (const pattern of op.patterns) {
                if (sourcePredicates.has(pattern.predicate.value)) {
                    patternResulting.push(pattern);
                }
            }
            const new_op = Util.mapOperation(op, {})
            new_op.patterns = patternResulting;
            return {
                result: new_op,
                recurse: false
            }
        },
        [Algebra.types.JOIN]: (op: Algebra.Join) => {
            const inputOfJoin = [];
            for (const el of op.input) {
                if (el.type === Algebra.types.PATH) {
                    Util.recurseOperation(op, {
                        [Algebra.types.LINK]: (op: Algebra.Link) => {
                            if (sourcePredicates.has(op.iri.value)) {
                                inputOfJoin.push(el)
                            }
                            return false;
                        }
                    });
                } else {
                    inputOfJoin.push(el);
                }
            }
            const new_op = Util.mapOperation(op, {});
            new_op.input = inputOfJoin;
            return {
                result: new_op,
                recurse: true
            }
        }
    }

    const relevantQuerySection = Util.mapOperation(query, operationModifier);

    return relevantQuerySection;
}

export function hasPropertyPath(query: Algebra.Operation): boolean {
    let hasPropertyPath = false;
    const hasPropertyPathFunc = (_op: Algebra.Operation) => {
        hasPropertyPath = true
        return !hasPropertyPath;
    };
    Util.recurseOperation(query, {
        [Algebra.types.INV]: hasPropertyPathFunc,
        [Algebra.types.SEQ]: hasPropertyPathFunc,
        [Algebra.types.ALT]: hasPropertyPathFunc,
        [Algebra.types.ZERO_OR_MORE_PATH]: hasPropertyPathFunc,
        [Algebra.types.ONE_OR_MORE_PATH]: hasPropertyPathFunc,
        [Algebra.types.ZERO_OR_ONE_PATH]: hasPropertyPathFunc,
        [Algebra.types.NPS]: hasPropertyPathFunc,
        [Algebra.types.LINK]: hasPropertyPathFunc,
    })
    return hasPropertyPath;
}

export interface IRelation {
    relation: string,
    argument_s: string,
    argument_o: string,
}

export type ConjectiveQuery = IRelation[];

export function convertSPARQLIntoRelationalAlgebra(query: Algebra.Operation): Result<ConjectiveQuery> {
    if (hasPropertyPath(query)) {
        return { error: "Do not support queries with property path currently" };
    }
    const relationalQuery: ConjectiveQuery = [];
    Util.recurseOperation(query, {
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
            const relation: IRelation = {
                relation: op.predicate.value,
                argument_s: op.subject.value,
                argument_o: op.object.value
            }
            relationalQuery.push(relation);
            return false;
        }
    })
    return { result: relationalQuery };
}

export function normalizeQueries(query1: Algebra.Operation, query2: Algebra.Operation): Result<INormalizeQueryResult> {
    const queryGraph1 = populateQueryGraph(query1);
    const queryGraph2 = populateQueryGraph(query2);
    const mapping: Map<string, string> = new Map();

    for (const tp1 of queryGraph1.associated_triple_patterns) {
        for (const tp2 of queryGraph2.associated_triple_patterns) {
            if (isomorphic([tp2], [tp1])) {
                for (const term of PATTERN_TERMS_NAME) {
                    if (tp1[term].termType === "BlankNode") {
                        mapping.set(tp2[term].value, tp1[term].value);
                    }
                }
                break;
            }
        }
    }

    const newQuery2 = renameVariableInQuery(query2, mapping);
    return {
        result: {
            queries: {
                query_1: query1,
                query_2: newQuery2
            },
            mapping
        }
    }

}

function renameVariableInQuery(query: Algebra.Operation, mapping: Map<string, string>): Algebra.Operation {

    return Util.mapOperation(query, {
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {

            for (const term of PATTERN_TERMS_NAME) {
                if (op[term].termType === "Variable") {
                    const normalizedVariable = mapping.get(op[term].value);
                    if (normalizedVariable !== undefined) {
                        op[term].value = normalizedVariable;
                    }
                }
            }


            return {
                result: op,
                recurse: false
            };
        },
        [Algebra.types.PROJECT]: (op: Algebra.Project) => {
            for (const variable of op.variables) {
                const normalizedVariable = mapping.get(variable.value);
                if (normalizedVariable !== undefined) {
                    variable.value = normalizedVariable;
                }
            }
            return {
                result: op,
                recurse: true
            }
        }
    });;
}

function populateQueryGraph(query: Algebra.Operation): IQueryGraph {
    const queryGraph: IQueryGraph = {
        relevant_variables: new Set<string>,
        associated_triple_patterns: new Array<Algebra.Pattern>
    };

    Util.recurseOperation(query, {
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {

            if (op.subject.termType === "Variable") {
                queryGraph.relevant_variables.add(op.subject.value);
            }
            if (op.predicate.termType === "Variable") {
                queryGraph.relevant_variables.add(op.predicate.value);
            }
            if (op.object.termType === "Variable") {
                queryGraph.relevant_variables.add(op.object.value);
            }
            if (op.object.termType === "Variable" ||
                op.predicate.termType === "Variable" ||
                op.subject.termType === "Variable"
            ) {
                const opWithBlankNode = changeVariableToBlankNode(op);
                queryGraph.associated_triple_patterns.push(opWithBlankNode)
            }
            return false;
        }
    });
    return queryGraph;
}

function changeVariableToBlankNode(op: Algebra.Pattern): Algebra.Pattern {
    const resp = <Algebra.Pattern>Util.mapOperation(op, {});

    for (const term of PATTERN_TERMS_NAME) {
        if (resp[term].termType === "Variable") {
            resp[term] = RDF_FACTORY.blankNode(resp[term].value);
        }
    }

    return resp;
}

interface IQueryGraph {
    relevant_variables: Set<string>,
    associated_triple_patterns: Algebra.Pattern[]
}

export interface INormalizeQueryResult {
    queries: {
        query_1: Algebra.Operation,
        query_2: Algebra.Operation
    },
    mapping: Map<string, string>
}

