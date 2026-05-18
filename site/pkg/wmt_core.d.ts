/* tslint:disable */
/* eslint-disable */

export class WmtEngine {
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Ingest pasted JSON. `{ok, errors, meta}`.
     */
    ingest(json: string): string;
    meta(): string;
    constructor();
    prompt(nl: string): string;
    reactivate(id: string): string;
    remove(id: string): string;
    retract(id: string): string;
    seed_demo(): string;
    /**
     * Clean sat/unsat/unknown check (run first).
     */
    smt_check(): string;
    /**
     * SMT-LIB2 with `get-unsat-core` (run only when smt_check is unsat).
     */
    smt_consistency(): string;
    /**
     * SMT-LIB2 to test whether the active set entails `term`.
     */
    smt_entails(term: string): string;
}

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_wmtengine_free: (a: number, b: number) => void;
    readonly wmtengine_ingest: (a: number, b: number, c: number) => [number, number];
    readonly wmtengine_meta: (a: number) => [number, number];
    readonly wmtengine_new: () => number;
    readonly wmtengine_prompt: (a: number, b: number, c: number) => [number, number];
    readonly wmtengine_reactivate: (a: number, b: number, c: number) => [number, number];
    readonly wmtengine_remove: (a: number, b: number, c: number) => [number, number];
    readonly wmtengine_retract: (a: number, b: number, c: number) => [number, number];
    readonly wmtengine_seed_demo: (a: number) => [number, number];
    readonly wmtengine_smt_check: (a: number) => [number, number];
    readonly wmtengine_smt_consistency: (a: number) => [number, number];
    readonly wmtengine_smt_entails: (a: number, b: number, c: number) => [number, number];
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
