import type { IRv } from "./specs";

export function instantiateTemplate(
  iriDeclaration: string,
  literalDeclarations: string,
  variableDeclaration: string,
  conjecture: string,
) {
  return `
; ------------ Sort and Predicate -------------------
(declare-sort RDFValue 0)
(declare-fun P (RDFValue RDFValue RDFValue RDFValue) Bool)
(declare-const <default_graph> RDFValue)

; ------------ IRIs ---------------------------------
${iriDeclaration}
; ------------ Literals -----------------------------
${literalDeclarations}
; ------------ Variables ----------------------------
${variableDeclaration}
; ------------ Conjecture ---------------------------
${conjecture}
; ------------ Check-Sat ----------------------------
(check-sat)
`;
}

export function instantiateQueryContainmentConjecture(
  subQueryStatements: string,
  superQueryStatements: string,
  superQueryVariablesDeclaration: string,
  projectionVariableAssoc: string,
) {
  return `(assert
	(and
${addTab(subQueryStatements, 2)}
	)
)

(assert 
	(not 
		(exists (${superQueryVariablesDeclaration})
			(and
${addTab(superQueryStatements, 4)}
${addTab(projectionVariableAssoc, 4)}
			)
		)
	)
)`;
}

export function projectionVariablesAssoc(rvs: IRv[]): string {
  const statements: string[] = [];
  for (const rv of rvs) {
    const statement = `(= ${rv.name} sub_${rv.name})`;
    statements.push(statement);
  }
  return statements.join("\n");
}

export function instantiateThetaConjecture(
  statements: string,
  relevantVariablesExistDef: string,
  relevantVariablesExternalAssoc: string,
): string {
  if (statements === "") {
    return "";
  }
  return `${instantiateTemplatePhiConjecture(statements)}

(assert
	(exists (${relevantVariablesExistDef})
		(and
			(and
${addTab(relevantVariablesExternalAssoc, 4)}
			)
			(not
				(and
${addTab(statements, 5)}
				)
			)
		)    
	)
)`;
}

export function instantiateTemplatePhiConjecture(statements: string): string {
  if (statements === "") {
    return "";
  }

  return `
(assert
	(and
${addTab(statements, 2)}
	)
)
`;
}

function addTab(statement: string, nTab: number): string {
  const arrayStatement = statement.split("\n");
  const tabs: string[] = [];

  for (let i = 0; i < nTab; i++) {
    tabs.push("\t");
  }

  const formatedStatement = arrayStatement
    .map((el) => {
      return `${tabs.join("")}${el}`;
    })
    .join("\n");
  return formatedStatement;
}

export function instatiateTemplateTriplePatternConjecture(
  statements: string[],
): string {
  if (statements.length === 0) {
    return "";
  }
  const stringStament = statements.join("\n");
  return `
(and
${stringStament}
)`;
}

export function instantiateTriplePatternStatementTemplate(
  subject: string,
  predicate: string,
  object: string,
): string {
  return `(or (P ${subject} ${predicate} ${object} <default_graph>))`;
}

export function local_var_declaration(rvs: IRv[], nonGlobalRv?: Set<string>): [string, string] {
  const declarations: string[] = [];
  const equalities: string[] = [];

  for (const rv of rvs) {
    const declaration = !nonGlobalRv?.has(rv.name)?`(<e_${rv.name}> RDFValue)`:`(<${rv.name}> RDFValue)`;
    declarations.push(declaration);
    if (!nonGlobalRv?.has(rv.name)) {
      const equality = `(= <e_${rv.name}> <${rv.name}>)`;
      equalities.push(equality);
    }
  }
  const declaration = declarations.join(" ");
  const equality = equalities.join("\n");

  return [declaration, equality];
}
