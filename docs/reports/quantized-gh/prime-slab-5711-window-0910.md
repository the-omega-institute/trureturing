# GPU prime-slab window (5,7,11), 2026-09-10

The completed caller run returned **1600 new raw rows: 456 CPU-Arb certified
negative outcomes and 1144 exactly inactive rows**. The stored classifications
contain no invalid, disagreeing or unresolved rows. All 456 active GPU proposals
are **indeterminate with underflow flags**; there are **zero definite GPU signs**.
These are the original run's results, aggregated without mathematical recertification.

This is the bounded report implementation for
`qgh0910-i34-gpu-5711-window-report`, attempt 1. The companion
[evidence record](prime-slab-5711-window-0910.json) embeds the complete original
runtime receipt and checkpoint as unchanged JSON values, retaining their
`prime-slab-raw-and-arb-v1` schema and identity labels. It binds all listed inputs
by path, byte size and SHA-256 and copies all eight active reflected records.
The complete C97 GoalArtifact remains unchanged: all 97 constraints and 51 success
criteria continue to apply. This assignment does not complete the standing goal.

The searched ranges are **inclusive**: boxes **148800..148863**, raw IDs
**3720000..3721599**, triple index **36**, primes **(5,7,11)**, exponents
**b0=5, b1=4..7, b2=0..15**. Each of the 64 boxes has all 25 slots, with no missing
or duplicate IDs. The encoding is `box_id=4096*t+256*b0+16*b1+b2` and
`row_id=25*box_id+slot`; slots 0..6 are adjacent and 7..24 reflected. The single
checkpoint chunk is `certified`, with `coverage_complete=true` and `next_box=148864`.
This covers the requested window within the earlier prospective design of
229376 boxes / 5734400 raw slots; it is not full-domain or full-campaign coverage.

| Kind | Raw slots | Active / CPU negative | Exactly inactive | Invalid | Disagreeing | Unresolved |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Adjacent | 448 | 448 | 0 | 0 | 0 | 0 |
| Reflected | 1152 | 8 | 1144 | 0 | 0 | 0 |
| Total | 1600 | 456 | 1144 | 0 | 0 | 0 |

The preregistered prediction of **448 active adjacent slots is confirmed** by
aggregation of stored classifications. Its recorded rationale was
`64*7; each R_lower>=5^5*7^4=7503125>5040`; that mathematical claim was not recomputed
here. Reflected activity and G signs were preregistered as unmeasured. The eight
reflected negatives are additional measured outcomes: 448 was an adjacent-slot
prediction, not a prediction of total active rows.

| Reflected row ID | Box | Slot | b0,b1,b2 | j,i | Recorded nearest_ties |
| ---: | ---: | ---: | --- | --- | --- |
| 3720072 | 148802 | 22 | 5,4,2 | 6,0 | [0] |
| 3720088 | 148803 | 13 | 5,4,3 | 3,0 | [0] |
| 3720092 | 148803 | 17 | 5,4,3 | 4,1 | [1] |
| 3720523 | 148820 | 23 | 5,5,4 | 6,1 | [1] |
| 3720539 | 148821 | 14 | 5,5,5 | 3,1 | [1] |
| 3720857 | 148834 | 7 | 5,6,2 | 1,0 | [0] |
| 3720924 | 148836 | 24 | 5,6,4 | 6,2 | [2] |
| 3721315 | 148852 | 15 | 5,7,4 | 3,2 | [2] |

All eight have `guard_bits=31`, `gpu_error_bits=4`, an `indeterminate` GPU proposal,
and one stored 128-bit `negative` CPU refinement. Their nonempty `nearest_ties`
metadata is preserved. The JSON copies each complete classified record: raw
hex float strings, exact audit integers/rationals, all interval endpoints for
G, D, Psi, L, H, M0, M1, V0, rho and ell, six mixtures, all weights, distance
ratios, ties and original anomaly fields. No interval string is rounded or
reconstructed. Source line numbers are one-based; the raw header adds one line.
All 456 active rows finished at 128 bits; the configured ladder was 128,256,512,
with zero extra precision evaluations. Inactive rows have empty refinement arrays:
the original run exactly audited their guards without analytically evaluating G.

This run belongs to the **corrected delivered program**, program SHA-256
`519acdc009869a00d18d918f5137ab035f717b220afbd1463a2ee9143e87dd5c`, input SHA-256
`9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672`, and runtime HEAD
`2ee40a714251977a35f70c0c277261ab9317fa86` on `lane/math/prime-slab-5711-run-0910`.
The supplied runtime pin and activation establish that worktree identity; this
worker did not access the runtime worktree. The seven program-file byte identities
and input match the delivered copies in the report worktree. The program digest
hashes the recorded file-to-SHA256 map, not the Git HEAD. The receipt preserves the
exact command, argv, dependency identities, environment, events and terminal status.

Caller host **47908** exited **0** for one bounded search dispatch of 1600 threads.
The receipt records `new_gpu_raw_rows=1600`, `new_cpu_audited_rows=1600`,
`recovered_gpu_raw_rows=0` and `verification_replay_rows=0`. The recorded command
below is provenance; it was **not executed by this report worker**:

```text
make -C tools prime-slab-search SLAB_FIRST=148800 SLAB_LAST=148863 SLAB_CHUNK=64 SLAB_MAX_CHUNKS=1 SLAB_STATE=/Users/auricstudio/.local/state/qgh-prime-slab-5711-0910
```

The recorded machine is Apple M3 Ultra, arm64, macOS 26.6.2, Python 3.12.13,
Torch 2.8.0, NumPy 2.0.2 and python-flint 0.8.0. `PYTORCH_ENABLE_MPS_FALLBACK=0`;
fast-math/prefer-Metal environment values are null, and Metal uses Torch 2.8
`compile_shader` defaults. There is no GPU roundoff certificate. Underflow bit 4
conservatively flags possible subnormal/flush-to-zero behavior on every active
row. Recorded integer-overflow, nonfinite and other flag counts are zero.
Finite negative GPU approximations and zero float tails cannot establish a
rigorous GPU sign.

| Recorded seconds | Value | Scope |
| --- | ---: | --- |
| GPU dispatch and synchronize | 0.012077957857400179 | Host monotonic wall time around kernel invocation and MPS synchronization; excludes tensor setup/readback |
| CPU verification | 0.0722249171230942 | Original audit and Arb-certification loop over 1600 returned rows, including 1144 inactive audits |
| Orchestration | 2.5700150409247726 | Total minus the two preceding measured scopes; setup/environment, compilation, readback and persistence within that total |
| Total | 2.654317915905267 | Entrypoint `run()` start through the final timer sample; excludes process startup, dependency installation and final receipt publication |

Recorded UTC timestamps are `2026-09-10T15:02:46.807163+00:00` through
`2026-09-10T15:02:49.459485+00:00`. They are separate from the monotonic total.
There is no hardware-only kernel timing, benchmark comparison, whole-campaign
speed estimate or report-worker timing claim.

External evidence remains under `/Users/auricstudio/.local/state/qgh-prime-slab-5711-0910/`:

| Relative path under state root | Bytes | Whole-file SHA-256 |
| --- | ---: | --- |
| `run-844b07e368574c8e8f6ce741ec5f2d8c.json` | 7157 | `e972f9251d473465127708de56627a896bfe0b70dcd545e3b58a24859fec5668` |
| `window-148800-148863/checkpoint.json` | 2485 | `4ee5afe3f727868dea37e043f3dff934eb1ff441dc0a122f440daea38df35bc7` |
| `window-148800-148863/raw-148800-148863.jsonl` | 366620 | `389c1fb9a97b99dcf7244c7c70bc250c1ec5f5f5060065a41a29199374b07e54` |
| `window-148800-148863/classified-148800-148863.jsonl` | 2784180 | `48221af8551c0c20a9414b34c7d8b508b06945f6e848660a8417713ec10791f8` |

The raw **whole-file hash** covers 1601 lines: one provenance header plus 1600
rows. The receipt's **normalized raw-stream hash** is
`1cea755d7428cb45f0a8a5aab2ea2c5fa450eec48a53c85d023ca32362edd3c6`.
It excludes the header and hashes each parsed row reserialized as UTF-8
`json.dumps(row, sort_keys=True, separators=(',', ':'), allow_nan=False) + LF`.
These hashes have different scopes and are not interchangeable. The classified
file has 1600 lines without a header; its whole-file and normalized stream hashes
coincide. Embedded receipt/checkpoint objects preserve every JSON value, not the
original whitespace; original byte hashes bind that distinction. All external
files remain untouched. This is local durable preservation, not an off-host backup claim.

The [historical pilot report](prime-slab-mps-pilot-0909.md) and its
[JSON evidence](prime-slab-mps-pilot-0909.json) remain byte-for-byte unchanged.
That pilot covered boxes 3072..3135 / raw IDs 76800..78399 for (2,3,5), with
450 CPU negatives and 1150 inactive rows under its **original program**
`27a15ae48802d7ad188b5f73e315d6230f0e6b7b208d96d351e6556a18c34ef0`.
There is no retroactive attribution to the corrected program. The supplied
historical delivery receipt records PR 6783's merge and historical successful
checks; those facts confer no review, CI success or merge status on this report.
Historical external streams were neither opened nor reverified. The two
documented local ranges are disjoint. Other-device ranges were never supplied,
so cross-device nonoverlap is not claimed.

The [existing finite design](../prime-slab-finite-design-0909.md) and
[constant atlas](../prime-slab-corner-order-0909.json) supply the mathematics.
**G = D - Psi compares two existing bounds; it is not an RH criterion**.
D is the maximum of six feasible fractional-knapsack mixtures, while
Psi = f(H) + 2 f(L), f(x) = log(1 - exp(-x)), using the existing slab and
nearest-endpoint definitions. Stored CPU G intervals concern the full unscaled
expression; the GPU proposes the 24-term scaled expression exp(min(c_i))*G.
The existing exact tail bound 3/104857600 covers truncation alone, not input,
transcendental, branch, clipping, summation, roundoff or underflow error.
Finite operational evidence is distinct from the earlier mathematical reduction.
This report establishes no complete-domain sign result, all-prime theorem, RH
result, novel theorem or formalization. The user's GH/RH context does not redefine G.

Prerequisites were read completely before either new file was written: local
AGENTS.md, target CLAUDE.md, supplied authority snapshot, agents/CONTEXT.md, pinned
sshx skill/spec, complete C97 GoalArtifact and listed new inputs. Skill/spec
hashes match their requested pins. One supplied identity claim differs: target
CLAUDE.md is the requested Git blob `3138b10dfc55b2e0c570da8079821518f36196eb`,
but the snapshot is actually `1392db0b7ee38fcadd4bda4c06af13a7a6806790`.
Only lines 621, 625 and 627 differ: snapshot CI stability thresholds are 12/36
versus target 8/16. The current target authority was used; both byte identities
and exact differing lines are retained in the JSON. This intake discrepancy is
not a search failure; neither authority file was edited. All carriers remain
fallible and this worker is repo-prior-exposed. This is implementation, not
independent review.

Fixed validation uses Python's standard library only: strict JSON, byte/hash
bindings, exact embedded-value equality, metadata links, contiguous ranges,
slot/exponent labels, counts, anomaly arrays and eight-record equality. It does
not derive guards or evaluate mathematical expressions. The exact fixed check
source is retained in the JSON; this command ran from the report worktree with exit 0:

```sh
python3 - <<'PY'
import json
from pathlib import Path
report = json.loads(Path('docs/reports/quantized-gh/prime-slab-5711-window-0910.json').read_bytes())
exec(compile(report['validation']['source'], '<fixed-5711-report-checks>', 'exec'))
PY
```

The result was `fixed_validation=pass`: 1600 rows, 64 boxes, eight reflected
records and both output byte identities. Read-only Git checks confirmed HEAD
`935d10335f7920a6a266191eaf8b8c0c3d132346`, branch
`lane/math/prime-slab-5711-report-0910`, an empty index and exactly these two
untracked additions. No tracked file changed. An initial shell heredoc parse
error occurred before either output existed; the write command was corrected.
There were no scientific execution failures or structural validation failures.

This worker ran no search, candidate generator, mathematical module, saved-stream
mathematical verifier, old certificate, historical replay, fixed-xi sweep, test
suite, mutation suite, build or ingest. No source re-ingest is needed for this
new experiment report. Independent review, caller sealing/commit, ordinary
applicable gates and eventual MERGED delivery of these two files remain
outstanding. The complete standing goal and its other stages remain caller-owned.
