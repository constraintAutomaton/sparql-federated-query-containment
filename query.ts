import { Algebra, Util } from 'sparqlalgebrajs';
import { type Result } from './util';
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

/**
 * Determine if the query does not contain operators that we do not support
 * @param {Algebra.Operation} query
 * @returns {boolean} return true if the query is supported
 */
export function isSupportedQuery(query: Algebra.Operation): boolean {
    return true;
}

export function isQueryAcycle(query: Algebra.Operation): boolean {
    return true;
}

export function isQueryWellDesigned(query: Algebra.Operation): boolean {
    return true;
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
