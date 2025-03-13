export function instantiatePhiTemplate(iriDeclaration:string, literalDeclarations:string, variableDeclaration:string, conjecture:string): string {
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

export function instantiateTemplatePhiConjecture(statements: string): string {
    return `
(assert
    (and
${statements}
    )
)
`;
}

export function instantiateTriplePatternStatementTemplate(subject: string, predicate: string, object: string): string {
    return `(or (P ${subject} ${predicate} ${object} <default_graph>))`;
}