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
import { isError, type Result } from "../util";
import { normalizeQueries } from "../query";
import * as RDF from 'rdf-js';
import { instantiatePhiTemplate, instantiateTemplatePhiConjecture, instantiateTriplePatternStatementTemplate } from "./templates";
import * as Z3_SOLVER from 'z3-solver';

const { Z3,
} = await Z3_SOLVER.init();

export function isContained(subQ: Algebra.Operation, superQ: Algebra.Operation): Result<boolean> {
    const normalizedQueriesOutput = normalizeQueries(superQ, subQ);
    if (isError(normalizedQueriesOutput)) {
        return normalizedQueriesOutput;
    }
    const normalizedSubQ = normalizedQueriesOutput.result.queries.sub_query;
    const normalizedSuperQ = normalizedQueriesOutput.result.queries.super_query;

    const subQRepresentation = generateQueryRepresentation(normalizedSubQ, "sub");
    const superQRepresentation = generateQueryRepresentation(normalizedSuperQ, "super");

    const tileCheckIsValid = performTildeCheck(subQRepresentation.rv, superQRepresentation.rv);
    if (tileCheckIsValid) {

    } else {
        const phiEvaluationSmtLibString = generatePhiSmtLibString(subQRepresentation.sigmas);
        let config = Z3.mk_config();
        let ctx = Z3.mk_context_rc(config);
        Z3.eval_smtlib2_string(ctx, phiEvaluationSmtLibString);
    }
    return { error: "not implemented" };
}

export function generatePhiSmtLibString(sigmas: Sigma[]): string {

    let iriDeclarations: string[] = [];
    let literalDeclarations: string[] = [];
    let variableDeclarations: string[] = [];

    const triplePatternsAssertions: string[] = [];

    for (const sigma of sigmas) {
        iriDeclarations = [...iriDeclarations, ...sigma.iriDeclarations];
        literalDeclarations = [...literalDeclarations, ...sigma.literalDeclarations];
        variableDeclarations = [...variableDeclarations, ...sigma.variableDeclarations];
        const triplePatternsStatementAssertion = instantiateTriplePatternStatementTemplate(sigma.subject, sigma.predicate, sigma.object);
        triplePatternsAssertions.push(triplePatternsStatementAssertion);
    }

    const iriDeclarationString = iriDeclarations.join("\n");
    const literalDeclarationsString = literalDeclarations.join("\n");
    const variableDeclarationsString = variableDeclarations.join("\n");

    const triplePatternsAssertionsString = triplePatternsAssertions.join("\n");

    const phiConjecture = instantiateTemplatePhiConjecture(triplePatternsAssertionsString);

    const instance = instantiatePhiTemplate(iriDeclarationString, literalDeclarationsString, variableDeclarationsString, phiConjecture);

    return instance;
}

/**
 * Perform the ∼ operation described in definition (4.8)
 * @param {Rv[]} subQRv - relevant variables of the sub query
 * @param {Rv[]} superQRv - relevant variables of the super query
 * @returns {boolean} if the operation is valid
 */
export function performTildeCheck(subQRv: Rv[], superQRv: Rv[]): boolean {
    const setRvSubQ = new Set(subQRv.map((el) => el.name));
    const setRvSuperQ = new Set(superQRv.map((el) => el.name));
    if (setRvSubQ.size != setRvSuperQ.size) {
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
 * @returns {{ ov: Ov[], rv: Rv[] }}
 */
export function generateOvRv(query: Algebra.Operation): { ov: Ov[], rv: Rv[] } {
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
        if (projectedVariables.has(variable)) {
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
    if (resp.includes("http://")) {
        resp = resp.replace("http://", "");
    }
    if (resp.includes("https://")) {
        resp = resp.replace("https://", "");
    }
    if (resp.includes("www.")) {
        resp = resp.replace("www.", "");
    }

    resp = resp.replaceAll(".", "_");
    resp = resp.replaceAll("/", "_");
    resp = resp.replaceAll("-", "_");

    return resp;
}

/**
 * An ov variable (definition 4.6)
 */
class Ov {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }
}

/**
 * A relevant variable (definition 4.6)
 */
class Rv {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }
}

type Sigma = ISigmaTerm;

interface ISigmaTerm {
    subject: string;
    predicate: string;
    object: string;

    iriDeclarations: string[];
    literalDeclarations: string[];
    variableDeclarations: string[];
}

class SigmaTerm implements ISigmaTerm {

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
        this.subject = this.addATermToTheDeclaration(subject, smtLibDeclaration);
        this.predicate = this.addATermToTheDeclaration(predicate, smtLibDeclaration);
        this.object = this.addATermToTheDeclaration(object, smtLibDeclaration);

        this.iriDeclarations = smtLibDeclaration.iri;
        this.literalDeclarations = smtLibDeclaration.literal;
        this.variableDeclarations = smtLibDeclaration.variable;
    }


    private addATermToTheDeclaration(term: RDF.Term, resp: { iri: string[], literal: string[], variable: string[] }): string {
        let constantName: string | undefined = undefined;
        if (term.termType === "NamedNode") {
            constantName = `<${renameIriforSmt(term.value)}>`
            resp.iri.push(`(declare-const	${constantName}	RDFValue)`);
        } else if (term.termType === "Literal") {
            constantName = `<l_${SigmaTerm.literalCounter}>`;
            SigmaTerm.literalCounter += 1;
            resp.literal.push(`(declare-const	${constantName}	RDFValue)`);
        } else if (term.termType === "Variable" || term.termType === "BlankNode") {
            constantName = `<${this.queryLabel}_${term.value}>`;
            resp.variable.push(`(declare-const	${constantName}	RDFValue)`);
        }
        if (constantName !== undefined) {
            return constantName;
        }
        throw new Error(`The term sent was not a NamedNode, a Literal or a Variable but was ${term.termType}`);
    }
}

interface IQueryRepresentation {
    sigmas: Sigma[];
    ov: Ov[];
    rv: Rv[];
}