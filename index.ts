import { translate, Algebra, Util } from 'sparqlalgebrajs';
import { normalizeQueries, type INormalizeQueryResult } from './query';
import { type Result, isResult } from './util';

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
const { result } = <{ result: INormalizeQueryResult }>resp

console.log(result);