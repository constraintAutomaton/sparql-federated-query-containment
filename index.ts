import { translate, Algebra, Util, toSparqlJs } from 'sparqlalgebrajs';
import { normalizeQueries, type INormalizeQueryResult } from './lib/query';
import { type Result, isResult } from './lib/util';

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


console.log(JSON.stringify(toSparqlJs(query1), null, 2));