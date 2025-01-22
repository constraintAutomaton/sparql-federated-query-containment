import { Algebra, Util } from 'sparqlalgebrajs';

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
            const new_op = Util.mapOperation(op,{})
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
            const new_op = Util.mapOperation(op,{});
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