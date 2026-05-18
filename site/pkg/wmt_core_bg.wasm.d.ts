/* tslint:disable */
/* eslint-disable */
export const memory: WebAssembly.Memory;
export const __wbg_wmtengine_free: (a: number, b: number) => void;
export const wmtengine_analyze_begin: (a: number) => void;
export const wmtengine_analyze_feed: (a: number, b: number, c: number) => void;
export const wmtengine_analyze_next: (a: number) => [number, number];
export const wmtengine_analyze_result: (a: number) => [number, number];
export const wmtengine_ingest: (a: number, b: number, c: number) => [number, number];
export const wmtengine_meta: (a: number) => [number, number];
export const wmtengine_new: () => number;
export const wmtengine_prompt: (a: number, b: number, c: number) => [number, number];
export const wmtengine_reactivate: (a: number, b: number, c: number) => [number, number];
export const wmtengine_remove: (a: number, b: number, c: number) => [number, number];
export const wmtengine_retract: (a: number, b: number, c: number) => [number, number];
export const wmtengine_seed_demo: (a: number) => [number, number];
export const wmtengine_set_weight: (a: number, b: number, c: number, d: bigint) => [number, number];
export const wmtengine_smt_check: (a: number) => [number, number];
export const wmtengine_smt_core: (a: number) => [number, number];
export const wmtengine_smt_entails_json: (a: number, b: number, c: number) => [number, number];
export const __wbindgen_externrefs: WebAssembly.Table;
export const __wbindgen_malloc: (a: number, b: number) => number;
export const __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
export const __wbindgen_free: (a: number, b: number, c: number) => void;
export const __wbindgen_start: () => void;
