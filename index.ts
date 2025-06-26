import { translate } from "sparqlalgebrajs";

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
const algebra_boy = translate(query);

console.log(JSON.stringify(algebra_boy, null, 2));