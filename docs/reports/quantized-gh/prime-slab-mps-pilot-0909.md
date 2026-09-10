# Prime-slab MPS implementation pilot, 2026-09-09

This is a bounded implementation-validation result. One MPS search returned all
1,600 preregistered raw rows. Python exact arithmetic checked membership for every
row; independent outward Arb evaluation certified all 450 active gaps as strictly
negative. The other 1,150 rows were exactly inactive. There are no missing,
duplicate, unresolved, invalid, or disagreeing rows in this pilot.

Implementation provenance: one Codex CLI implementation worker, under the
caller-supplied sshx implementation brief; no local skill, child worker, or oracle
was invoked. The implementation and its self-checks are not independent review.
The worktree base is `6428a0eb9032978f091ec6668e2a49a2275e0f09`, branch
`lane/math/quantized-gpu-0908`. Git and PR operations remain caller-owned.

The mathematical inputs are the supplied GPT-6 Astra sharpening primary, task
`3609e6b0-ab4d-4891-9b0f-55c613d43942`, conversation
`conv_4c0b62a5e14b0f64`, and preceding all-real-slab primary task
`ce312694-86a6-4a1b-8318-90c77dc28f75`. Their conclusion objects were read; their
log references remained opaque. These are primary paper inputs under separate
source implementation/review, not independently approved GPU code. The live S13
and S14/I9 targets and peer logs were not accessed. No merged S14 source is
presupposed here. GH retains the user's literal label; no new definition is made.

The constant input is [prime-slab-corner-order-0909.json](../prime-slab-corner-order-0909.json),
an exact copy of the supplied 6,741-byte certificate, SHA-256
`9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672`.
Its 56 prime triples, primality, mask completeness, subset products and strict
corner ordering are checked before use. CPU input preparation generates no
exponent boxes. The byte identity is deliberately pinned as a scientific input
certificate, including its provenance; it is not a performance-cache key.

The prospective domain is all increasing triples from `[2,3,5,7,11,13,17,19]`
and independent exponents `b0,b1,b2` in `0..15`: 229,376 boxes, 25 slots per box,
5,734,400 raw rows. The raw slot totals are 1,605,632 adjacent and 4,128,768
reflected. Activity is not assumed from those totals. Metal decodes
`box_id=4096*t+256*b0+16*b1+b2` and `row_id=25*box_id+slot` and constructs the
integer guard operands on the device. Host scheduling supplies bounded ranges,
not exponent-box arrays.

The preregistration, written before any device kernel execution, is
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qgh0909-i10-prime-slab-gpu/attempt-1/pilot-preregistration.json`
(SHA-256 `1468dcf5fc5627a343b3b4f85b518aca09c3a3b6668cffe277464d78308cada7`).
It fixes boxes **3072..3135**, triple `(2,3,5)`, `b0=12`, `b1=0..3`, `b2=0..15`,
and raw rows **76800..78399**. There was one pilot execution and **zero pilot
reruns**. No additional exponent-box window was searched.

| Slot type | Raw | Active, certified negative | Exactly inactive |
| --- | ---: | ---: | ---: |
| Adjacent | 448 | 447 | 1 |
| Reflected | 1,152 | 3 | 1,149 |
| Total | 1,600 | 450 | 1,150 |

Every active row resolved at 128 bits; the bounded ladder was `128,256,512`.
There were zero escalations, positive results, weak-sign results, exact-zero
labels, or unresolved results. The complete row count includes inactive rows
whose guards were independently checked, not unreturned or synthesized rows.

All 450 active GPU outputs had a finite negative 24-term scaled value, but all
also carried the conservative possible-underflow flag. Consequently **all 450
GPU sign proposals were indeterminate**. The GPU issued zero definite active
signs. Zero definite-proposal sign disagreements is therefore not evidence of
float32 sign accuracy. Integer parameters and guard proposals agreed with Python
exact arithmetic on all 1,600 rows. Integer overflow and nonfinite-error flags
were both zero. CPU certificates evaluate the full expression and never use
underflowed values or the GPU tail as proof.

The three active reflected rows are 77041 (box 3081, slot 16), 78093 (box 3123,
slot 18), and 78191 (box 3127, slot 16). Their exact nearest-distance ties are
at coordinates 0, 2, and 0, respectively. Their `exp(T1)` values are, respectively,
`147573952589676412928/2197265625`, `476837158203125/3981312`, and
`147573952589676412928/2373046875`. Each denominator exceeds one. The static
[summary JSON](prime-slab-mps-pilot-0909.json) retains their exact rational outward
gap bounds and references the complete stream; they were not replaced by corner
budgets.

The implementation is `tools/scripts/agent/prime_slab_search.py` with four focused
Python helpers and `prime_slabs/search.metal`. The Metal guards use 64 base-256
limbs in unsigned 32-bit integers. A limb multiply plus carry is bounded by
`255*19+18=4863`; the carry remains at most 18. Every production operand is at
most `19^102 < 2^510 < 256^64` (`19^102` has bit length 434), and each reflected
single-prime exponent is at most 99. Carry out of the final limb sets an explicit
error. All five reflected comparisons and the 5040 cutoff are strict integer
comparisons. Logs and float32 values cannot activate a slot. No IDs are deduplicated.

For each active slot, Metal evaluates all six knapsack permutations, including
clipping, then takes the maximum normalized 24-term sum. This retains secant
ties, integral optima and upper saturation. The analytical uniform tail
`6*2^(-23)/25 = 3/104857600` bounds truncation only. GPU input, transcendental,
branch, rounding and underflow errors have not been rigorously bounded.

For CPU certification, write `q0=exp(M0)` and `q1=exp(M1)` as exact positive
rationals. An endpoint `log(z)` lies below the interval exactly when `z^3<q0`
and above it exactly when `z^3>q1`. Its distance is thus one third of the log of
an exact rational ratio, or exactly zero. Comparing those ratios selects the
nearest endpoint and identifies exact ties. Similarly, every permutation's
clipping is settled by comparing `q1/(prod(C)*prefix)` with 1 and the endpoint
ratio `D_i/C_i`. Arb evaluates the selected exact expression with outward
`log`, `exp`, `log1p`, `sqrt`, arithmetic and maximum operations; it encloses all
six feasible mixtures. No interval overlap is used as equality. Zero variance
is handled without division by the radius. Strict, weak and unresolved signs
are distinct; no exact-zero label is inferred from an interval touching zero.
Each refinement retains rational outward endpoints, six mixture enclosures,
weights, exact distance ratios, tie coordinates and the precision used.

Runtime data are external under
`/Users/auricstudio/.local/state/qgh-prime-slab-pilot-0909`.
The program directly reuses unchanged `gpu5040/state_store.py`: `StateLocks`
acquires the external state lock, then shared `gpu-verifier.lock`, with
nonblocking failure. Locks are never unlinked or forced. The existing xi and
gpu5040 programs and targets were not changed or executed.

Raw chunks are durably written before verification, even if subsequent coverage
checks fail. Classified chunks become checkpoint entries only after every raw
row has its audit result. Incomplete data are not certified. Resume consumes a
durably returned pending raw chunk or dispatches distinct remaining chunks;
completed chunks are not resubmitted. Source/input/schema/precision identities,
stream digests, ordered IDs and stored counts are checked before reuse. A source
change requires a distinct state directory or an explicit identity failure; no
old result is silently promoted. There is no controller, daemon or CPU generator.

The ordered raw stream SHA-256, excluding each chunk's provenance header, is
`8645467ae1f9c651e0897eacee90eb94cb9bf1b1dff0c5bf5396532a41311f1c`.
The ordered complete classification stream SHA-256 is
`d6135c038e970072caffda3394c38759c86aff2982c1023733c02c5ef0f0a288`.
Both hash canonical newline-terminated JSON row records, including every slot.
Raw float32 results are retained losslessly as hexadecimal float strings,
including explicit `nan` in unused inactive fields. Whole-file hashes, byte
sizes, program-file hashes and exact artifact paths are in the static summary.

Program identity: `27a15ae48802d7ad188b5f73e315d6230f0e6b7b208d96d351e6556a18c34ef0`.
Kernel identity: `1305d0a1c9afd3d986f0d435ec3e8205d916ae951ff84420183e7ba1861b3e9d`.
The program identity hashes the production Python/Metal closure and reused state
store, not a Git commit or this report. Runtime dependency and input identities
are bound separately. The tested device was **Apple M3 Ultra**, macOS 26.6.2,
arm64; uv Python 3.12.13, Torch 2.8.0, NumPy 2.0.2 and python-flint 0.8.0.
`PYTORCH_ENABLE_MPS_FALLBACK=0` was set before Torch import. Actual MPS availability
and tensor placement were asserted. `compile_shader` used its Torch 2.8 defaults;
no claim is made that float compiler optimizations establish an error bound.

| Pilot timing scope | Seconds |
| --- | ---: |
| Dispatch plus `torch.mps.synchronize()` wall time | 0.013361625 |
| CPU row verification | 0.070080125 |
| Orchestration, compile, transfer and publication | 2.166869625 |
| Total measured runner interval | 2.250311375 |

The GPU timing is synchronized host wall time, not a hardware execution counter.
It is one small-window observation, not a full-campaign performance claim.

The device probes were one invocation with four custom Metal dispatches:
`limb_probe` (6 fixtures, including 512-bit overflow), `guard_probe` (6 fixtures,
cutoff and four equality boundaries), `decode_probe` (5 IDs: 0, 102399, 102400,
5734399 and 76800; decoding only), and `numerical_probe` (3 synthetic real grids,
including tied slopes, zero variance, saturation and a nearest-distance tie).
All passed on their first invocation. The numerical probe's `1e-4` tolerance is
an API sanity check, not a rigorous GPU rounding certificate. Its actual inputs,
outputs and expected comparisons are retained in
`run-07fc9cfff7004db8bb7526b0346e0b3b.json`. Torch's internal allocation/copy
dispatches were not counted as custom Metal probes or searched rows.

The final CPU suite has 19 passing scientific/durability tests. Four in-memory
mutations produced exactly the six preregistered named test failures, with zero
compile errors or test errors, and restored the production functions and source
identities. Their six-tuples and logs are in
`mutations-9216fd9206ce46a48373c886cbbb5862.json` and its referenced files.
The suite checks strict guards, complete IDs, corrupted proposals, verification
of negative and inactive proposals, bounded uncertainty, exact ties, saturation,
input/program mismatch, incomplete accounting, publication failure, locks,
distinct-chunk resume and prohibition of CPU fallback.

Validation failures are preserved in the summary. The initial TDD run failed
because the package did not yet exist. One test initially mistook Arb's outward
radius for a zero-touching interval; the verifier's unresolved result was correct.
The first mutation harness patched only a module attribute and missed an imported
coverage-function alias. The second harness attempt reached the shared function
but `unittest.mock` failed to restore its `__code__` descriptor. Explicit
try/finally restoration corrected the test harness. The two mutation-harness
corrections occurred after the pilot and changed tests only; the production
program and kernel stayed identical.
No failed device probe or pilot rerun is being omitted.

Reproducible canonical commands, run from this worktree (all final exits 0):

```sh
make -C tools prime-slab-test
make -C tools prime-slab-mutation-test
make -C tools prime-slab-device-test
make -C tools prime-slab-search SLAB_FIRST=3072 SLAB_LAST=3135
make -C tools prime-slab-verify SLAB_FIRST=3072 SLAB_LAST=3135
```

The saved-stream verify invocation matched all 1,600 classifications and made
zero GPU dispatches (`run-d187fb7a3b8a4771bcf331549ec9ce67.json`). Its 1,600 CPU
rechecks add **zero new searched coverage**. The original pilot receipt is
`run-3b4080403bf740519c99c60aca54b2c2.json`. Reusing the search command with its
completed checkpoint does not resubmit the pilot. Arbitrary bounded windows use
explicit `SLAB_FIRST`, `SLAB_LAST`, `SLAB_CHUNK`, `SLAB_MAX_CHUNKS`, and a separate
`SLAB_STATE` when changing source or scientific identity. `SLAB_MAX_CHUNKS=0`
finishes the explicit window; a positive value returns a resumable checkpoint.

Independent implementation review, canonical CI and MERGED delivery remain
required. The current FILEMAP classifies `tools/scripts/**` as judge and
`docs/reports/**` as content; the caller must settle the SL-029 publication
partition through the canonical gates. No admission/CI verdict or Git/PR mutation
was performed by this worker. The remaining **229,312 boxes / 5,732,800 raw rows**
(boxes `0..3071` and `3136..229375`) are unsearched. No C25 coordinate-separation
hypothesis was used for pruning. This pilot establishes no all-prime truth, RH
result, formal/Lean theorem, full campaign completion, or completion of the
standing research goal.

---

## Placement and provenance — 2026-09-10 (C65)

Current canonical paths are [docs/reports/quantized-gh/prime-slab-mps-pilot-0909.md](prime-slab-mps-pilot-0909.md) and [docs/reports/quantized-gh/prime-slab-mps-pilot-0909.json](prime-slab-mps-pilot-0909.json). The [constant input](../prime-slab-corner-order-0909.json) is unchanged. Moving the pair adds no direct `docs/reports` files under the recorded 48-file admission bound.

Immutable inputs: the [original Markdown](https://github.com/the-omega-institute/trureturing/blob/e6d0a14439b0c13593ce70471d1aed05b2099811/docs/reports/prime-slab-mps-pilot-0909.md) and [original JSON](https://github.com/the-omega-institute/trureturing/blob/e6d0a14439b0c13593ce70471d1aed05b2099811/docs/reports/prime-slab-mps-pilot-0909.json) remain at the original report commit. The [original program entry point](https://github.com/the-omega-institute/trureturing/blob/2116fafbfeaa374ae3c40adede73229623c44bee/tools/scripts/agent/prime_slab_search.py), [Python/Metal helpers](https://github.com/the-omega-institute/trureturing/tree/2116fafbfeaa374ae3c40adede73229623c44bee/tools/scripts/agent/prime_slabs), [shared state-store source](https://github.com/the-omega-institute/trureturing/blob/2116fafbfeaa374ae3c40adede73229623c44bee/tools/scripts/agent/gpu5040/state_store.py) and [original constant input](https://github.com/the-omega-institute/trureturing/blob/2116fafbfeaa374ae3c40adede73229623c44bee/docs/reports/prime-slab-corner-order-0909.json) are pinned to the original program commit.

The preceding body, commands, program/source/stream/checkpoint identities, results, failures, timings, resource limits and caller/worker/actual-PRO provenance are historical receipts of the original program. All 450 active negatives were CPU-certified; all 450 active GPU proposals remain indeterminate. The later corrected program has a different identity; this note does not attribute the historical stream to corrected-code execution.

This Codex CLI I21 representation repair uses pinned `consensus-rnd:sshx` `1.0.0-beta.42` with repository prior exposed. The original 209-line body is preserved except one three-byte `../` insertion in its constant-input link; the summary bytes are exact. Only bounded byte, link, scope and directory-count checks were performed, with zero mathematical, test-suite, search or GPU executions. The original report's two approvals and one comment are prior-stage history. Fresh independent review of this representation and ordinary publication gates remain caller-owned; content delivery still waits for the corrected judge program to reach MERGED. This repair makes no new research, independent-review, CI-green or MERGED claim.

---

## Summary schema provenance — 2026-09-10 (C77)

The [summary JSON](prime-slab-mps-pilot-0909.json) now presents this historical pilot as `prime-slab-pilot-report-v2`, with the numeric count `cpu_certification.unresolved_count: 0`. The former `unresolved: 0` collided with SL-019's reserved anomaly key: numeric values reach `IsOpen`'s default `true` branch. This is a descriptive report-schema repair; the original execution did not emit v2. Runtime `identity.schema` remains `prime-slab-raw-and-arb-v1`, with no legacy alias added.

The immutable [v1 JSON](https://github.com/the-omega-institute/trureturing/blob/099da11b6b2f73579e4910d7c03ac33521c4651e/docs/reports/quantized-gh/prime-slab-mps-pilot-0909.json) and [pre-repair Markdown](https://github.com/the-omega-institute/trureturing/blob/099da11b6b2f73579e4910d7c03ac33521c4651e/docs/reports/quantized-gh/prime-slab-mps-pilot-0909.md) remain addressable at commit `099da11b6b2f73579e4910d7c03ac33521c4651e`. All 15,820 preceding Markdown bytes (221 LF; SHA-256 `b6e2a43793ae5e245ca807dc7eebeea6d46ff045177efb667b8beb0a9ba07475`) are retained exactly, including existing relative links.

| JSON representation | Bytes | LF | SHA-256 |
| --- | ---: | ---: | --- |
| Historical v1 at the immutable commit above | 12,949 | 396 | `43990ef3037a0e46dacf3e9a287cf6732a8553c2d3744460f1229b5d314900ff` |
| Current v2 presentation | 12,955 | 396 | `52b151e12ee9347632e02ba219f960b4300e90d6caa4a9b42440bc0c19ef2db0` |

The exact inverse has two edits: remove the six ASCII bytes `_count` at zero-based byte offset 3404 from `cpu_certification.unresolved_count`; then change the final digit of the sole descriptive schema value `prime-slab-pilot-report-v2` from `2` to `1` at recovered offset 11296 (v2 offset 11302 before removal). These edits recover every original JSON byte; both variants parse, and reversing the key/schema mapping preserves every original value.

Earlier “current”, “unchanged”, exact-summary, command/status, review and CI assertions retain their original I10/C65 representation-snapshot scope. The original r2 approvals cover only the immutable BASE above and do not approve v2; preserved JSON status and residuals remain historical statements, with no new closure inferred. All 450 active GPU proposals remain indeterminate; CPU-Arb certified 450 negatives and 1,150 rows were inactive. Every measurement, failure, range and original source/input/program/stream identity is preserved. This I26 Codex CLI repair under pinned `consensus-rnd:sshx` beta.42 used only fixed structural checks, with no new search or revalidation. Fresh independent full-report representation review, ordinary CI and MERGED delivery remain caller-owned and are not claimed here. All original scientific residuals and the standing goal remain unchanged.
