import { translate } from "sparqlalgebrajs";
import {isContained, SEMANTIC} from "./dist";
import * as Z3_SOLVER from "z3-solver";

const Z3 = await Z3_SOLVER.init();

const superQ = translate(`
PREFIX rh: <http://rdf.rhea-db.org/>
PREFIX up: <http://purl.uniprot.org/core/>

SELECT ?uniprot ?mnemo ?rhea ?accession ?equation
WHERE {
  SERVICE <https://sparql.uniprot.org/sparql> {
      #VALUES (?rhea) { (<http://rdf.rhea-db.org/11312>) (<http://rdf.rhea-db.org/11313>) }
      ?uniprot up:reviewed true .
      ?uniprot up:mnemonic ?mnemo .
      ?uniprot up:organism ?taxid .
      ?uniprot up:annotation/up:catalyticActivity/up:catalyzedReaction ?rhea . # where ?rhea comes from query upwards
  }
  ?rhea rh:accession ?accession .
  ?rhea rh:equation ?equation .
}`);

const subQ = translate(`
PREFIX rh: <http://rdf.rhea-db.org/>
PREFIX up: <http://purl.uniprot.org/core/>

SELECT ?uniprot ?mnemo ?rhea ?accession ?equation
WHERE {
  SERVICE <https://sparql.uniprot.org/sparql> {
      #VALUES (?rhea) { (<http://rdf.rhea-db.org/11312>) (<http://rdf.rhea-db.org/11313>) }
      ?uniprot up:reviewed true .
      ?uniprot up:mnemonic ?mnemo .
      ?uniprot up:organism ?taxid .
      ?uniprot up:annotation/up:catalyticActivity/up:catalyzedReaction ?rhea . # where ?rhea comes from query upwards
      ?taxid <http://purl.uniprot.org/core/strain> <http://purl.uniprot.org/taxonomy/10090#strain-752F89669B9A8D5A40A7219990C3010B>.
  }
  ?rhea rh:accession ?accession .
  ?rhea rh:equation ?equation .
}`);

const option = {
      semantic: SEMANTIC.BAG_SET,
      z3: Z3,
      sources: []
    };

const resp = await isContained(subQ, superQ, option)
console.log(resp);