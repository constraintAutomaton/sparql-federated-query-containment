import { Algebra } from 'sparqlalgebrajs';
import * as RDF from '@rdfjs/types';


export interface IMaterializedView {
    query: Algebra.Operation,
    results: RDF.Quad[],
}

export type MaterializedViewIndex = IMaterializedView[];
