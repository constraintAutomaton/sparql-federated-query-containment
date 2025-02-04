export type Result<Val, Error = string> = { result: Val } | { error: Error };

export function isResult<Val, Error>(value: Result<Val, Error>): value is { result: Val } {
    return 'result' in value;
}

export function isError<Val, Error>(value: Result<Val, Error>): value is { error: Error } {
    return 'error' in value;
}