import { translate, Algebra, Util } from 'sparqlalgebrajs';

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

const obj = translate(query);

const callbacks = {
    [Algebra.types.BGP]: (op: Algebra.Bgp) => {
        // console.log(op)
        // console.log("---")
        const patternResulting = [];
        for (const pattern of op.patterns) {
            if (pattern.predicate.termType)
                if (pattern.predicate.value !== "http://purl.uniprot.org/core/annotation") {
                    patternResulting.push(pattern);
                }
        }
        const new_op = Util.mapOperation(op,{});
        new_op.patterns = patternResulting;
        return {
            result: new_op,
            recurse: false
        }
    },
    [Algebra.types.JOIN]: (op: Algebra.Join) => {
        const inputOfJoin = [];
        for (const el of op.input){
            if(el.type === Algebra.types.PATH){
                Util.recurseOperation(op, {
                    [Algebra.types.LINK]: (op:Algebra.Link)=>{
                        if(op.iri.value === "http://rdf.rhea-db.org/chebi"){
                             
                        }
                        return false;
                    }
                });
            }else{
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


const mappedOperations = Util.mapOperation(obj, callbacks);

console.log(JSON.stringify(mappedOperations, null, 2));