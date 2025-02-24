import { Algebra, Util } from "sparqlalgebrajs";
import type { Result } from "../util";


export function generateSigmas(query: Algebra.Operation): Result<Sigma[]> {
    const result: Sigma[] = [];
    Util.recurseOperation(query, {
        [Algebra.types.PATTERN]: (op: Algebra.Pattern) => {
            const sigma: ISigmaTerm = new SigmaTerm(
                op.subject.value,
                op.predicate.value,
                op.object.value
            );
            result.push(sigma);
            return false;
        }
    });
    return { result };
}

export function generateOvRv(query: Algebra.Operation): Result<{ ov: Ov[], rv: Rv[] }> {
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
        const rv = new Rv(variable);
        result.rv.push(rv);
    }
    return { result }
}

class Ov implements IToSmtFragment {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }

    public toSmtFragment(): string {
        return "";
    }
}

class Rv implements IToSmtFragment {
    public readonly name: string;

    public constructor(name: string) {
        this.name = name;
    }

    public toSmtFragment(): string {
        return "";
    }
}

type Sigma = ISigmaTerm;

interface ISigmaTerm extends IToSmtFragment {
    subject: string,
    predicate: string,
    object: string
}

class SigmaTerm implements ISigmaTerm {
    public readonly subject: string;
    public readonly predicate: string;
    public readonly object: string;

    public constructor(subject: string, predicate: string, object: string) {
        this.subject = subject;
        this.predicate = predicate;
        this.object = object;
    }
    public toSmtFragment(): string {
        return "";
    }
}

interface IToSmtFragment {
    toSmtFragment: () => string;
}