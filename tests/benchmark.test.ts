import { describe, expect, it,test } from "vitest";
import { readFile } from 'fs/promises';
import { Algebra, translate } from "sparqlalgebrajs";
import * as Z3_SOLVER from "z3-solver";
import { isContained, ISolverOption, ISolverResponse, SEMANTIC } from "../lib/specs";
import { isResult, Result } from "result-interface";
import { readdir, stat } from 'fs/promises';
import path from 'path';

const Z3 = await Z3_SOLVER.init();

describe("specs", async () => {
    const option: ISolverOption = {
        semantic: SEMANTIC.SET,
        z3: Z3,
        sources: []
    };

    const nopFiles = await getAllTestFiles("./tests/specs_test_cases/nop");
    const pFiles = await getAllTestFiles("./tests/specs_test_cases/p");

    test.each(nopFiles)('%s', async (file)=>{
        const { subQ, superQ } = await parseQuery(file);
        const expected = await expectedResponse(file);
        const respOrErr = await isContained(subQ, superQ, option);

        expect(respOrErr).toEqual(
            expect.objectContaining({
                value: expect.objectContaining({
                    result: expected
                })
            })
        );
    });

    test.each(pFiles)('%s', async (file)=>{
        const { subQ, superQ } = await parseQuery(file);
        const expected = await expectedResponse(file);
        const respOrErr = await isContained(subQ, superQ, option);

        expect(respOrErr).toEqual(
            expect.objectContaining({
                value: expect.objectContaining({
                    result: expected
                })
            })
        );
    });
});

async function getAllTestFiles(dir:string): Promise<string[]> {

    const entries = await readdir(dir);
    const result: string[] = [];

    for (const entry of entries) {
        const fullPath = path.join(dir, entry);
        const stats = await stat(fullPath);
        if (stats.isFile() && path.extname(entry).toLowerCase() !== '.json') {
            result.push(fullPath);
        }
    }

    return result;
}

async function expectedResponse(file: string): Promise<boolean> {
    const result = JSON.parse((await readFile(file + ".json")).toString());
    return result.result;
}
async function parseQuery(file: string): Promise<{ subQ: Algebra.Operation; superQ: Algebra.Operation; }> {
    const RE = /(?:(?<type>subquery|superquery)):\s*(?<query>[\s\S]*?)(?=\n\s*(?:subquery|superquery):|$)/gi;
    const text = (await readFile(file)).toString();
    const option = { baseIRI: "http://www.example.org/" };
    let subQ: Algebra.Operation | undefined;
    let superQ: Algebra.Operation | undefined;

    for (const match of text.matchAll(RE)) {
        if (match.groups !== undefined) {
            if (match.groups.type === "subquery") {
                subQ = translate(match.groups.query.trim(), option);
            } else if (match.groups.type === "superquery") {
                superQ = translate(match.groups.query.trim(), option);
            }
        }
    }

    if (subQ === undefined || superQ === undefined) {
        throw new Error(`query file ${file} is not valid`);
    }
    return { subQ, superQ };
}