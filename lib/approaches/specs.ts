/**
 * Partial implementation of the SpeCS paper following the explanation of the paper "Solving the SPARQL query containment problem with SpeCS"
 * SPASIĆ, Mirko; JANIČIĆ, Milena Vujošević. Solving the SPARQL query containment problem with SpeCS. Journal of Web Semantics, 2023, 76: 100770.
 * https://doi.org/10.1016/j.websem.2022.100770
 * 
 * The reference to definition are from the paper above.
 * 
 * Official implementation
 * https://github.com/mirkospasic/SpeCS
 */
import { Algebra, Util } from "sparqlalgebrajs";
import { normalizeQueries } from "../query";
import type * as RDF from '@rdfjs/types';
import {  instantiateThetaConjecture, instantiateThetaTemplate, instantiateTriplePatternStatementTemplate, local_var_declaration } from "./templates";
import * as Z3_SOLVER from 'z3-solver';
import { type SafePromise, result, error } from "result-interface";

const { Z3,
} = await Z3_SOLVER.init();

export async function isContained(subQ: Algebra.Operation, superQ: Algebra.Operation): SafePromise<boolean, string> {
    // make so the queries share the same variable names
    const normalizedQueriesOutput = normalizeQueries(superQ, subQ);

    const normalizedSubQ = normalizedQueriesOutput.queries.sub_query;
    const normalizedSuperQ = normalizedQueriesOutput.queries.super_query;

    // generate the variable of the specs formalisum
    const subQRepresentation = generateQueryRepresentation(normalizedSubQ, "sub");
    const superQRepresentation = generateQueryRepresentation(normalizedSuperQ, "super");

    const tileCheckIsValid = tildeCheck(subQRepresentation.rv, superQRepresentation.rv);
    if (tileCheckIsValid) {
        return error("not implemented");
    }
    const thetaEvaluationSmtLibString = generateThetaSmtLibString(subQRepresentation.sigmas, subQRepresentation.rv);
    let config = Z3.mk_config();
    let ctx = Z3.mk_context_rc(config);
    console.log(thetaEvaluationSmtLibString);
    const response = await Z3.eval_smtlib2_string(ctx, thetaEvaluationSmtLibString);
    if (response.startsWith("sat")) {
        return result(true);
    } else if (response.startsWith("unsat")) {
        return result(false);
    }
    return error(`Z3 returns ${response}`);

}

export function generateThetaSmtLibString(sigmas: Sigma[], rvs: IRv[]): string {

    let iriDeclarations: string[] = [];
    let literalDeclarations: string[] = [];
    let variableDeclarations: string[] = [];

    const triplePatternsAssertions: string[] = [];

    for (const sigma of sigmas) {
        iriDeclarations = [...iriDeclarations, ...sigma.iriDeclarations];
        literalDeclarations = [...literalDeclarations, ...sigma.literalDeclarations];
        variableDeclarations = [...variableDeclarations, ...sigma.variableDeclarations];
        const triplePatternsStatementAssertion = instantiateTriplePatternStatementTemplate(sigma.subject, sigma.predicate, sigma.object);
        triplePatternsAssertions.push(`${triplePatternsStatementAssertion}`);
    }

    const iriDeclarationString = Array.from(new Set(iriDeclarations)).join("\n");
    const literalDeclarationsString = Array.from(new Set(literalDeclarations)).join("\n");
    const variableDeclarationsString = Array.from(new Set(variableDeclarations)).join("\n");

    const triplePatternsAssertionsString = triplePatternsAssertions.join("\n");

    const [localVarDeclaration, localVarAssoc] = local_var_declaration(rvs);
    const thetaConjecture = instantiateThetaConjecture(triplePatternsAssertionsString, localVarDeclaration, localVarAssoc);

    const instance = instantiateThetaTemplate(iriDeclarationString, literalDeclarationsString, variableDeclarationsString, thetaConjecture);

    return instance;
}

/**
 * Perform the ∼ operation described in definition (4.8)
 * @param {IRv[]} subQRv - relevant variables of the sub query
 * @param {IRv[]} superQRv - relevant variables of the super query
 * @returns {boolean} if the operation is valid
 */
export function tildeCheck(subQRv: IRv[], superQRv: IRv[]): boolean {
    const setRvSubQ = new Set(subQRv.map((el) => el.name));
    const setRvSuperQ = new Set(superQRv.map((el) => el.name));
    if (setRvSubQ.size !== setRvSuperQ.size) {
        return false;
    }
    for (const el of setRvSubQ) {
        if (!setRvSuperQ.has(el)) {
            return false;
        }
    }
    return true;
}

function generateQueryRepresentation(query: Algebra.Operation, queryLabel: string): IQueryRepresentation {
    const sigmas = generateSigmas(query, queryLabel);
    const ovRv = generateOvRv(query);
    return {
        sigmas,
        ...ovRv
    }
}

/**
 * generate the sigma terms representing the expression of the query see Definition 4.2 and 4.4
 * @param {Algebra.Operation} query 
 * @returns {Sigma[]}
 */
export function generateSigmas(query: Algebra.Operation, queryLabel: string): Sigma[] {
    const result: Sigma[] = [];
    Util.recurseOperation(query, {
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
            const sigma: ISigmaTerm = new SigmaTerm(
                op.subject,
                op.predicate,
                op.object,
                queryLabel
            );
            result.push(sigma);
            return false;
        }
    });
    return result;
}

/**
 * generate the relevant variables rv (definition 4.6) and the ov variables (definition 4.5)
 * @param {Algebra.Operation} query 
 * @returns {{ ov: IOv[], rv: IRv[] }}
 */
export function generateOvRv(query: Algebra.Operation): { ov: IOv[], rv: IRv[] } {
    const result: { ov: Ov[], rv: Rv[] } = {
        ov: [],
        rv: []
    };
    const projectedVariables: Set<string> = new Set();
    const usedVariables: Set<string> = new Set();

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
    const usedButNotProjected = [];
    for (const variable of usedVariables) {
        if (!projectedVariables.has(variable)) {
            usedButNotProjected.push(variable);
        }
    }

    for (const variable of usedButNotProjected) {
        const ov = new Ov(variable);
        result.ov.push(ov);
    }
    for (const variable of usedVariables) {
        if (projectedVariables.has(variable)) {
            const rv = new Rv(variable);
            result.rv.push(rv);
        }
    }
    return result;
}

export function renameIriforSmt(iri: string): string {
    let resp = iri;
    resp = resp.replace("http://", "");
    resp = resp.replace("https://", "");
    resp = resp.replace("www.", "");


    resp = resp.replaceAll(".", "_");
    resp = resp.replaceAll("/", "_");
    resp = resp.replaceAll("-", "_");
    resp = resp.replaceAll("%", "_");
    resp = resp.replaceAll("#", "_");

    return resp;
}

/**
 * An ov variable (definition 4.6)
 */
export interface IOv {
    name: string;
}

class Ov implements IOv {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }
}

/**
 * A relevant variable (definition 4.6)
 */
export interface IRv {
    name: string
}

class Rv implements IRv {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }
}
/**
 * A sigma function (definition 4.4)
 */
export type Sigma = ISigmaTerm;

/**
 * A sigma function (definition 4.4 Term)
 */
export interface ISigmaTerm {
    subject: string;
    predicate: string;
    object: string;

    iriDeclarations: string[];
    literalDeclarations: string[];
    variableDeclarations: string[];
}

export class SigmaTerm implements ISigmaTerm {

    private static literalCounter = 0;
    public readonly queryLabel: string;

    public readonly subject: string;
    public readonly predicate: string;
    public readonly object: string;

    public readonly iriDeclarations: string[];
    public readonly literalDeclarations: string[];
    public readonly variableDeclarations: string[];


    public constructor(subject: RDF.Term, predicate: RDF.Term, object: RDF.Term, queryLabel: string) {
        this.queryLabel = queryLabel;

        const smtLibDeclaration: { iri: string[], literal: string[], variable: string[] } = {
            iri: [],
            literal: [],
            variable: []
        };
        this.subject = this.generateSMTlibTerm(subject);
        this.predicate = this.generateSMTlibTerm(predicate);
        this.object = this.generateSMTlibTerm(object);

        this.addATermToTheDeclaration(subject, this.subject, smtLibDeclaration);
        this.addATermToTheDeclaration(predicate, this.predicate, smtLibDeclaration);
        this.addATermToTheDeclaration(object, this.object, smtLibDeclaration);

        this.iriDeclarations = smtLibDeclaration.iri;
        this.literalDeclarations = smtLibDeclaration.literal;
        this.variableDeclarations = smtLibDeclaration.variable;
    }

    public static generateDeclareSmtLibString(constantName: string): string {
        return `(declare-const ${constantName} RDFValue)`;
    }

    private generateSMTlibTerm(term: RDF.Term): string {
        if (term.termType === "NamedNode") {
            return `<${renameIriforSmt(term.value)}>`
        } else if (term.termType === "Literal") {
            const name = `<l_${SigmaTerm.literalCounter}>`;
            SigmaTerm.literalCounter += 1;
            return name
        } else if (term.termType === "Variable" || term.termType === "BlankNode") {
            return `<${this.queryLabel}_${term.value}>`;
        }
        throw new Error(`The term sent was not a NamedNode, a Literal or a Variable but was ${term.termType}`);
    }

    private addATermToTheDeclaration(term: RDF.Term, constantName: string, resp: { iri: string[], literal: string[], variable: string[] }) {
        const constanceDeclaration = SigmaTerm.generateDeclareSmtLibString(constantName);

        if (term.termType === "NamedNode") {
            resp.iri.push(constanceDeclaration);
        } else if (term.termType === "Literal") {
            resp.literal.push(constanceDeclaration);
        } else if (term.termType === "Variable" || term.termType === "BlankNode") {
            resp.variable.push(constanceDeclaration);
        }
    }
}

interface IQueryRepresentation {
    sigmas: Sigma[];
    ov: Ov[];
    rv: Rv[];
}