/**
 * Function to manipulate or determine the properties of queries
 */
import { Algebra, Util } from 'sparqlalgebrajs';
import { RDF_FACTORY } from './util';
import { isomorphic } from "rdf-isomorphic";

const PATTERN_TERMS_NAME: (keyof Algebra.Pattern)[] = ["subject", "predicate", "object", "graph"];

export function queryVariables(query: Algebra.Operation): Set<string> {
    const variables: Set<string> = new Set();

    Util.recurseOperation(query, {
        [Algebra.types.SERVICE]: (_op: Algebra.Service) => {
            return false;
        },
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
            if (op.subject.termType === "Variable") {
                variables.add(op.subject.value);
            }
            if (op.predicate.termType === "Variable") {
                variables.add(op.predicate.value);
            }
            if (op.object.termType === "Variable") {
                variables.add(op.object.value);
            }
            return true;
        }
    });
    return variables;
}

export function hasProjection(query: Algebra.Operation): boolean {
    const projectedVariables = new Set();
    const usedVariables = new Set();

    Util.recurseOperation(query, {
        [Algebra.types.PROJECT]: (op: Algebra.Project) => {
            for (const variable of op.variables) {
                projectedVariables.add(variable.value);
            }
            return true;
        },
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
            if (op.subject.termType === "Variable") {
                usedVariables.add(op.subject.value);
            }
            if (op.predicate.termType === "Variable") {
                usedVariables.add(op.predicate.value);
            }
            if (op.object.termType === "Variable") {
                usedVariables.add(op.object.value);
            }
            return false;
        }
    });


    if (projectedVariables.size !== usedVariables.size) {
        return true;
    }
    for (const v of projectedVariables) {
        if (!usedVariables.has(v)) {
            return false;
        }
    }
    return false;
}
/**
 * Check if a query has property paths
 * @param {Algebra.Operation} query 
 * @returns {boolean}
 */
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

/**
 * Change the name of the variable of subQuery for does of superQuery
 * @param {Algebra.Operation} superQuery 
 * @param {Algebra.Operation} subQuery 
 * @returns {Result<INormalizeQueryResult>} 
 */
export function normalizeQueries(superQuery: Algebra.Operation, subQuery: Algebra.Operation): INormalizeQueryResult {
    const superQueryGraph1 = populateQueryGraph(superQuery);
    const subQueryGraph2 = populateQueryGraph(subQuery);
    const mapping: Map<string, string> = new Map();

    for (const tp1 of superQueryGraph1.associated_triple_patterns) {
        for (const tp2 of subQueryGraph2.associated_triple_patterns) {
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

    const newQuery2 = renameVariableInQuery(subQuery, mapping);
    return {
        queries: {
            super_query: superQuery,
            sub_query: newQuery2
        },
        mapping
    }

}
/**
 * Rename the variable of a query based on a mapping
 * @param {Algebra.Operation} query 
 * @param { Map<string, string>} mapping - the keys are the variable of the query and the values are the values to be replaced by
 * @returns {Algebra.Operation}
 */
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

/**
 * Create a query graph
 * @param {Algebra.Operation} query 
 * @returns {IQueryGraph}
 */
function populateQueryGraph(query: Algebra.Operation): IQueryGraph {
    const queryGraph: IQueryGraph = {
        relevant_variables: new Set<string>,
        associated_triple_patterns: new Array<Algebra.Pattern>,
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
                // change the variables to blank node so that the isomorphic algorithm works
                const opWithBlankNode = changeVariableToBlankNode(op,);
                queryGraph.associated_triple_patterns.push(opWithBlankNode);
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
    relevant_variables: Set<string>;
    associated_triple_patterns: Algebra.Pattern[];
}

/**
 * The result of a query normalization operation
 */
export interface INormalizeQueryResult {
    queries: {
        super_query: Algebra.Operation,
        sub_query: Algebra.Operation
    },
    /**
     * The keys are the variables from the sub query and the value the variable from the super query
     */
    mapping: Map<string, string>
}

