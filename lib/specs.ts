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
import type * as RDF from "@rdfjs/types";
import {
  instantiateThetaConjecture,
  instantiateTemplate,
  instantiateTriplePatternStatementTemplate,
  local_var_declaration,
  instantiateQueryContainmentConjecture,
} from "./templates";
import * as Z3_SOLVER from "z3-solver";
import { type SafePromise, result, error, isError } from "result-interface";
import { hasProjection, queryVariables } from "./query";
import { type IOptions } from 'sparql-cache-client';

interface ISolverError {
  error: string;
  smt?: string
}

export type Z3_FN = Z3_SOLVER.Z3HighLevel & Z3_SOLVER.Z3LowLevel;

export interface ISolverOption extends IOptions {
  semantic: SEMANTIC,
  z3: Z3_FN
}

export interface IUnionResponses {
  valid: ISolverResponse[];
  invalid: ISolverResponse[];
}

export interface ISolverResponse {
  result: boolean;
  smtlib?: string;
  justification?: string;
  nestedResponses?: Record<string, ISolverResponse>;
  unionResponses?: IUnionResponses;
}

export enum SEMANTIC {
  SET,
  BAG_SET,
  BAG,
}

export async function isContained(
  subQ: Algebra.Operation,
  superQ: Algebra.Operation,
  option: ISolverOption,
): SafePromise<ISolverResponse, ISolverError> {
  // generate the variable of the specs formalism
  const subQRepresentation = generateQueryRepresentation(subQ);
  const superQRepresentation = generateQueryRepresentation(superQ);

  switch (option.semantic) {
    case SEMANTIC.SET:
      return setSemanticContainment(subQRepresentation, superQRepresentation, option.z3);
    case SEMANTIC.BAG_SET:
      if (hasProjection(subQ)) {
        return bagSetSemanticContainment(
          subQRepresentation,
          superQRepresentation,
          option.z3
        );
      }
      return setSemanticContainment(subQRepresentation, superQRepresentation, option.z3);
    case SEMANTIC.BAG:
      return bagSemanticContainment(subQRepresentation, superQRepresentation, option.z3);
  }
}

async function bagSemanticContainment(subQRepresentation: IQueryRepresentation,
  superQRepresentation: IQueryRepresentation,
  z3: Z3_FN): SafePromise<ISolverResponse, ISolverError> {
  const subQuery = {
    variables: subQRepresentation.variables,
    relevantVariables: subQRepresentation.rv,
    sigmas: subQRepresentation.sigmas
  };
  const superQuery = {
    variables: superQRepresentation.variables,
    relevantVariables: superQRepresentation.rv,
    sigmas: superQRepresentation.sigmas
  };

  const tildeCheckIsValid = tildeCheckBag(subQuery, superQuery);
  return abstractContainment(
    tildeCheckIsValid,
    subQRepresentation,
    superQRepresentation,
    z3
  );
}

async function bagSetSemanticContainment(
  subQRepresentation: IQueryRepresentation,
  superQRepresentation: IQueryRepresentation,
  z3: Z3_FN
): SafePromise<ISolverResponse, ISolverError> {
  const subVariable = {
    variables: subQRepresentation.variables,
    relevantVariables: subQRepresentation.rv,
  };
  const superVariable = {
    variables: superQRepresentation.variables,
    relevantVariables: superQRepresentation.rv,
  };

  const tildeCheckIsValid = tildeCheckBagSet(subVariable, superVariable);
  return abstractContainment(
    tildeCheckIsValid,
    subQRepresentation,
    superQRepresentation,
    z3
  );
}

async function setSemanticContainment(
  subQRepresentation: IQueryRepresentation,
  superQRepresentation: IQueryRepresentation,
  z3: Z3_FN,
  ignoreTilde?: boolean
): SafePromise<ISolverResponse, ISolverError> {
  const tildeCheckIsValid = ignoreTilde === true ? true : tildeCheck(
    subQRepresentation.rv,
    superQRepresentation.rv,
  );
  return abstractContainment(
    tildeCheckIsValid,
    subQRepresentation,
    superQRepresentation,
    z3
  );
}

function associateServiceClauses(
  subService: IService[],
  superService: IService[],
): IServiceQueryAssoc[] {
  const subQ: Map<string, IService> = new Map(
    subService.map((el) => [el.url, el]),
  );
  const superQ: Map<string, IService> = new Map(
    superService.map((el) => [el.url, el]),
  );
  const assoc: IServiceQueryAssoc[] = [];

  for (const [key, subService] of subQ) {
    const superService = superQ.get(key)!;

    const rv = relevantVariableService(superService, subService);
    subService.query.rv = rv;
    superService.query.rv = rv;

    const current: IServiceQueryAssoc = {
      subQ: subService.query,
      superQ: superService.query,
      url: key,
    };

    assoc.push(current);
  }

  return assoc;
}

function relevantVariableService(
  service1: IService,
  service2: IService,
): IRv[] {
  const rv1 = service1.query.variables;
  const rv2 = service2.query.variables;

  const intersection = rv1.intersection(rv2);
  return Array.from(intersection).map((el) => {
    return { name: el };
  });
}

export function compatibleValueClause(subValues: IValues, superValues: IValues): boolean {
  if(Object.keys(superValues).length === 0){
    return true;
  }
  if (Object.keys(subValues).length < Object.keys(superValues).length) {
    return false;
  }
  for (const [key, values] of Object.entries(subValues)) {
    if (superValues[key] === undefined) {
      return false;
    }
    for (const v of values) {
      if (!superValues[key].has(v)) {
        return false;
      }
    }
  }
  return true;
}

async function abstractContainment(
  compatibilityCheck: boolean,
  subQRepresentation: IQueryRepresentation,
  superQRepresentation: IQueryRepresentation,
  z3: Z3_FN
): SafePromise<ISolverResponse, ISolverError> {
  const { Z3 } = z3;

  if (
    !compatibleServiceClauses(
      subQRepresentation.service,
      superQRepresentation.service,
    )
  ) {
    return result({
      result: false,
      justification:
        "queries does not have the same URL for the service clauses",
    });
  }

  if(!compatibleValueClause(subQRepresentation.values, superQRepresentation.values)){
    return result({
      result: false,
      justification:
        "Queries does not have compatible VALUE clauses",
    });
  }

  const serviceAssoc = associateServiceClauses(
    subQRepresentation.service,
    superQRepresentation.service,
  );

  const intermediaryResults: Record<string, ISolverResponse> = {};

  for (const { subQ, superQ, url } of serviceAssoc) {
    const res = await setSemanticContainment(subQ, superQ, z3, true);
    if (isError(res)) {
      return res;
    }
    if (res.value.result === false) {
      intermediaryResults[url] = res.value;
      return result({
        result: false,
        justification: `service at url ${url} is not contained`,
        nestedResponses: intermediaryResults,
      });
    }
    intermediaryResults[url] = res.value;
  }

  if (emptyQuery(superQRepresentation)) {
    if (Object.keys(intermediaryResults).length === 0) {
      return result({
        result: false,
        justification: "the super query have no first level BGP",
      });
    }
    if (compatibilityCheck) {
      return result({ result: true, nestedResponses: intermediaryResults });
    }
    return result({ result: false, nestedResponses: intermediaryResults });
  }

  if (emptyQuery(subQRepresentation)) {
    return result({ result: true, nestedResponses: intermediaryResults });
  }

  if (compatibilityCheck) {
    const unionResponses: IUnionResponses = {
      valid: [],
      invalid: []
    };

    for (const sub_branch of subQRepresentation.union?.branches ?? []) {
      let validBranch: boolean = false;
      const superBranches = superQRepresentation.union?.branches ?? [];
      for (const super_branch of [...superBranches, superQRepresentation]) {
        const res = await setSemanticContainment(sub_branch, super_branch, z3, true);
        if (isError(res)) {
          return res;
        }
        if (res.value.result === false) {
          unionResponses.invalid.push(res.value);
        } else {
          validBranch = true;
          unionResponses.valid.push(res.value);
          break;
        }
      }
      if (!validBranch) {
        return result({
          result: false,
          nestedResponses: intermediaryResults,
          unionResponses: unionResponses,
          justification: "not every union branch was contained"
        });
      }
    }
    const queryContainmentSmtLibString = generateQueryContainment(
      subQRepresentation.sigmas,
      subQRepresentation.rv,
      superQRepresentation.sigmas,
      superQRepresentation.rv,
    );
    const config = Z3.mk_config();
    const ctx = Z3.mk_context_rc(config);
    const response = await Z3.eval_smtlib2_string(
      ctx,
      queryContainmentSmtLibString,
    );
    if (response.startsWith("unsat")) {
      return result({
        result: true,
        smtlib: queryContainmentSmtLibString,
        nestedResponses: intermediaryResults,
        unionResponses: unionResponses
      });
    } else if (response.startsWith("sat")) {
      return result({
        result: false,
        smtlib: queryContainmentSmtLibString,
        nestedResponses: intermediaryResults,
        unionResponses: unionResponses
      });
    }
    return error({ error: `Z3 returns ${response}`, smt: queryContainmentSmtLibString });
  }

  const thetaEvaluationSmtLibString = generateThetaSmtLibString(
    subQRepresentation.sigmas,
    subQRepresentation.rv,
  );
  const config = Z3.mk_config();
  const ctx = Z3.mk_context_rc(config);
  const response = await Z3.eval_smtlib2_string(
    ctx,
    thetaEvaluationSmtLibString,
  );
  if (response.startsWith("unsat")) {
    return result({ result: false, smtlib: thetaEvaluationSmtLibString });
  } else if (response.startsWith("sat")) {
    return result({ result: true, smtlib: thetaEvaluationSmtLibString });
  }
  return error({ error: `Z3 returns ${response}`, smt: thetaEvaluationSmtLibString });
}

export function compatibleServiceClauses(
  subService: IService[],
  superService: IService[],
): boolean {
  const subUrls = new Set(subService.map((el) => el.url));
  const superUrls = new Set(superService.map((el) => el.url));

  for (const url of subUrls) {
    if (!superUrls.has(url)) {
      return false;
    }
  }
  return true;
}

function emptyQuery(representation: IQueryRepresentation): boolean {
  return representation.sigmas.length === 0;
}

function generateQueryContainment(
  sub_sigmas: Sigma[],
  sub_rvs: IRv[],
  super_sigmas: Sigma[],
  super_rvs: IRv[],
): string {
  const subSigmaVar = sub_sigmas.map((el) => el.variables).flat();
  const superSigmaVar = super_sigmas.map((el) => el.variables).flat();

  const superQueryUniqueVar = variableOnlySuperQuery(subSigmaVar, superSigmaVar);

  const {
    iri: subIriDeclarationString,
    literal: subLiteralDeclarationsString,
    variable: subVariableDeclarationsString,
    tp: subTriplePatternsAssertions,
  } = generatePrelude(sub_sigmas);

  const {
    iri: superIriDeclarationString,
    literal: superLiteralDeclarationsString,
    variable: superVariableDeclarationsString,
    tp: superTriplePatternsAssertions,
  } = generatePrelude(super_sigmas, superQueryUniqueVar);

  const subTriplePatternsAssertionsString =
    subTriplePatternsAssertions.join("\n");
  const superTriplePatternsAssertionsString =
    superTriplePatternsAssertions.join("\n");

  const superSigmaVariables = new Set(super_sigmas.map((sigma) => sigma.variables).flat())

  const localVar = [];
  for (const v of super_rvs) {
    if (superSigmaVariables.has(v.name)) {
      localVar.push(v);
    }
  }

  for (const v of superQueryUniqueVar) {
    localVar.push({ name: v });
  }
  const [local_declaration, local_equality] = local_var_declaration(localVar, superQueryUniqueVar);

  const conjecture = instantiateQueryContainmentConjecture(
    subTriplePatternsAssertionsString,
    superTriplePatternsAssertionsString,
    local_declaration,
    local_equality,
  );

  const iris = Array.from(
    new Set([...subIriDeclarationString, ...superIriDeclarationString]),
  ).join("\n");
  const literals = Array.from(
    new Set([
      ...subLiteralDeclarationsString,
      ...superLiteralDeclarationsString,
    ]),
  ).join("\n");
  const variables = Array.from(
    new Set([
      ...subVariableDeclarationsString,
      ...superVariableDeclarationsString,
    ]),
  ).join("\n");

  const instance = instantiateTemplate(iris, literals, variables, conjecture);
  return instance;
}

function generatePrelude(sigmas: Sigma[], ignoreVariable?: Set<string>): {
  iri: string[];
  literal: string[];
  variable: string[];
  tp: string[];
} {

  let iriDeclarations: string[] = [];
  let literalDeclarations: string[] = [];
  let variableDeclarations: string[] = [];

  const triplePatternsAssertions: string[] = [];

  for (const sigma of sigmas) {
    iriDeclarations = [...iriDeclarations, ...sigma.iriDeclarations.map((el) => el.declaration)];
    literalDeclarations = [
      ...literalDeclarations,
      ...sigma.literalDeclarations.map((el) => el.declaration),
    ];
    if (ignoreVariable === undefined) {
      variableDeclarations = [
        ...variableDeclarations,
        ...sigma.variableDeclarations.map((el) => el.declaration),
      ];
    } else {
      for (const v of sigma.variableDeclarations) {
        if (!ignoreVariable.has(v.term)) {
          variableDeclarations.push(v.declaration);
        }
      }
    }


    const triplePatternsStatementAssertion =
      instantiateTriplePatternStatementTemplate(
        sigma.subject,
        sigma.predicate,
        sigma.object,
      );
    triplePatternsAssertions.push(triplePatternsStatementAssertion);
  }

  return {
    iri: iriDeclarations,
    literal: literalDeclarations,
    variable: variableDeclarations,
    tp: triplePatternsAssertions,
  };
}

function variableOnlySuperQuery(subQ: string[], superQ: string[]): Set<string> {
  const setSubQVar = new Set(subQ);

  const unique: Set<string> = new Set();

  for (const el of superQ) {
    if (!setSubQVar.has(el)) {
      unique.add(el);
    }
  }
  return unique;
}

export function generateThetaSmtLibString(sigmas: Sigma[], rvs: IRv[]): string {
  const {
    iri: iriDeclarationString,
    literal: literalDeclarationsString,
    variable: variableDeclarationsString,
    tp: triplePatternsAssertions,
  } = generatePrelude(sigmas);

  const triplePatternsAssertionsString = triplePatternsAssertions.join("\n");

  const [localVarDeclaration, localVarAssoc] = local_var_declaration(rvs);
  const thetaConjecture = instantiateThetaConjecture(
    triplePatternsAssertionsString,
    localVarDeclaration,
    localVarAssoc,
  );

  const instance = instantiateTemplate(
    Array.from(new Set(iriDeclarationString)).join("\n"),
    Array.from(new Set(literalDeclarationsString)).join("\n"),
    Array.from(new Set(variableDeclarationsString)).join("\n"),
    thetaConjecture,
  );

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

export function tildeCheckBagSet(
  subVariables: { variables: Set<string>; relevantVariables: IRv[] },
  superVariables: { variables: Set<string>; relevantVariables: IRv[] },
): boolean {
  const respSetCheck = tildeCheck(
    subVariables.relevantVariables,
    superVariables.relevantVariables,
  );
  if (!respSetCheck) {
    return false;
  }
  return superVariables.variables.isSupersetOf(subVariables.variables);
}

export function tildeCheckBag(subQuery: { variables: Set<string>; relevantVariables: IRv[]; sigmas: Sigma[] },
  superQuery: { variables: Set<string>; relevantVariables: IRv[]; sigmas: Sigma[] }): boolean {
  const resp = tildeCheckBagSet(subQuery, superQuery);
  if (!resp) {
    return false;
  }
  return superQuery.sigmas.length >= subQuery.sigmas.length;
}

function generateQueryRepresentation(
  query: Algebra.Operation,
): IQueryRepresentation {
  const sigmas = generateSigmas(query);
  const ovRv = generateOvRv(query);
  const variables = queryVariables(query);
  const service = generateService(query);
  //const union = generateUnion(query);
  const values = generateValues(query);
  return {
    sigmas,
    variables,
    ...ovRv,
    service,
    //union,
    values
  };
}

function generateUnion(query: Algebra.Operation): IUnion | undefined {
  let union: IUnion | undefined;
  Util.recurseOperation(query, {
    [Algebra.types.SERVICE]: () => false,
    [Algebra.types.UNION]: (op: Algebra.Union) => {
      union = new Union(op);
      return false;
    }
  });
  return union;
}

function generateService(query: Algebra.Operation): IService[] {
  const serviceOperations: IService[] = [];
  Util.recurseOperation(query, {
    [Algebra.types.SERVICE]: (op: Algebra.Service) => {
      const service = new Service(op.input, op.name.value);
      serviceOperations.push(service);
      return true;
    },
    [Algebra.types.UNION]: () => false
  });

  return serviceOperations;
}
/**
 * generate the sigma terms representing the expression of the query see Definition 4.2 and 4.4
 * @param {Algebra.Operation} query
 * @returns {Sigma[]}
 */
export function generateSigmas(query: Algebra.Operation): Sigma[] {
  const result: Sigma[] = [];
  Util.recurseOperation(query, {
    [Algebra.types.SERVICE]: () => false,
    [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
      const sigma: ISigmaTerm = new SigmaTerm(
        op.subject,
        op.predicate,
        op.object,
      );
      result.push(sigma);
      return false;
    },
    [Algebra.types.UNION]: () => false
  });
  return result;
}
export function generateValues(query: Algebra.Operation): IValues {
  const resp: IValues = {};

  Util.recurseOperation(query, {
    [Algebra.types.SERVICE]: () => false,
    [Algebra.types.VALUES]: (op: Algebra.Values) => {
      for (const binding of op.bindings) {
        for (const [key, val] of Object.entries(binding)) {
          if (resp[key] === undefined) {
            resp[key] = new Set([val.value]);
          } else {
            resp[key].add(val.value);
          }
        }
      }
      return false;
    },
    [Algebra.types.UNION]: () => false
  });
  return resp;
}

/**
 * generate the relevant variables rv (definition 4.6) and the ov variables (definition 4.5)
 * @param {Algebra.Operation} query
 * @returns {{ ov: IOv[], rv: IRv[] }}
 */
export function generateOvRv(query: Algebra.Operation): {
  ov: IOv[];
  rv: IRv[];
} {
  const result: { ov: Ov[]; rv: Rv[] } = {
    ov: [],
    rv: [],
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
    },
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
export interface IUnion {
  branches: IQueryRepresentation[]
}

export class Union implements IUnion {
  public readonly branches: IQueryRepresentation[] = [];

  public constructor(union: Algebra.Union) {
    for (const branch of union.input) {
      const branchRepresentation = generateQueryRepresentation(branch);
      branchRepresentation.rv = Array.from(branchRepresentation.variables).map((el) => {
        return { name: el };
      });

      this.branches.push(branchRepresentation);
    }
  }
}

export interface IService {
  url: string;
  query: IQueryRepresentation;
}

export class Service implements IService {
  public readonly url: string;
  public readonly query: IQueryRepresentation;

  public constructor(query: Algebra.Operation, url: string) {
    this.url = url;
    this.query = generateQueryRepresentation(query);
    this.query.rv = Array.from(this.query.variables).map((el) => {
      return { name: el };
    });
  }
}
/**
 * A relevant variable (definition 4.6)
 */
export interface IRv {
  name: string;
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

export interface IDeclaration {
  declaration: string,
  term: string
}
/**
 * A sigma function (definition 4.4 Term)
 */
export interface ISigmaTerm {
  subject: string;
  predicate: string;
  object: string;

  iriDeclarations: IDeclaration[];
  literalDeclarations: IDeclaration[];
  variableDeclarations: IDeclaration[];

  variables: string[];
}

export class SigmaTerm implements ISigmaTerm {
  private static literalCounter = 0;
  private static literalMap: Map<string, number> = new Map();

  public readonly subject: string;
  public readonly predicate: string;
  public readonly object: string;

  public readonly variables: string[];

  public readonly iriDeclarations: IDeclaration[];
  public readonly literalDeclarations: IDeclaration[];
  public readonly variableDeclarations: IDeclaration[];

  public constructor(subject: RDF.Term, predicate: RDF.Term, object: RDF.Term) {
    const smtLibDeclaration: {
      iri: IDeclaration[];
      literal: IDeclaration[];
      variable: IDeclaration[];
    } = {
      iri: [],
      literal: [],
      variable: [],
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

    this.variables = SigmaTerm.generateVariables(subject, predicate, object);
  }

  private static generateVariables(subject: RDF.Term, predicate: RDF.Term, object: RDF.Term): string[] {
    const variables: string[] = [];

    if (subject.termType === "Variable") {
      variables.push(subject.value);
    }

    if (predicate.termType === "Variable") {
      variables.push(predicate.value);
    }

    if (object.termType === "Variable") {
      variables.push(object.value);
    }

    return variables;
  }

  public static generateDeclareSmtLibString(constantName: string): string {
    return `(declare-const ${constantName} RDFValue)`;
  }

  private generateSMTlibTerm(term: RDF.Term): string {
    if (term.termType === "NamedNode") {
      return `<${renameIriforSmt(term.value)}>`;
    } else if (term.termType === "Literal") {
      const cache = SigmaTerm.literalMap.get(term.value);
      let value = SigmaTerm.literalCounter
      if (cache !== undefined) {
        value = cache;
      } else {
        SigmaTerm.literalMap.set(term.value, value);
        SigmaTerm.literalCounter += 1;
      }
      const name = `<l_${value}>`;
      return name;
    } else if (term.termType === "Variable" || term.termType === "BlankNode") {
      return `<${term.value}>`;
    }
    throw new Error(
      `The term sent was not a NamedNode, a Literal or a Variable but was ${term.termType}`,
    );
  }

  private addATermToTheDeclaration(
    term: RDF.Term,
    constantName: string,
    resp: { iri: IDeclaration[]; literal: IDeclaration[]; variable: IDeclaration[] },
  ): void {
    const constanteDeclaration =
      SigmaTerm.generateDeclareSmtLibString(constantName);

    if (term.termType === "NamedNode") {
      resp.iri.push({ declaration: constanteDeclaration, term: term.value });
    } else if (term.termType === "Literal") {
      resp.literal.push({ declaration: constanteDeclaration, term: term.value });
    } else if (term.termType === "Variable" || term.termType === "BlankNode") {
      resp.variable.push({ declaration: constanteDeclaration, term: term.value });
    }
  }
}

interface IQueryRepresentation {
  sigmas: Sigma[];
  variables: Set<string>;
  ov: Ov[];
  rv: Rv[];
  service: IService[];
  union?: IUnion
  values: IValues;
}

interface IServiceQueryAssoc {
  subQ: IQueryRepresentation;
  superQ: IQueryRepresentation;
  url: string;
}

interface IValues {
  [key: string]: Set<string>;
}