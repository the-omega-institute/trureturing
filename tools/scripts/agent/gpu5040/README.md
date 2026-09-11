# GPU Trial History

Portable foreground Apple MPS search for the fixed real stationary isometry
occupation target `(4,2,1,1)`. The Householder parameterization, occupation DP,
Adam updates and independent NumPy CPU full-word verifier are retained from
the original research program. A scalar numerical result is not a proof of
exact attainability, exhaustive search, a quantum impossibility, or a bound.

## Prerequisites

Python 3.9 or later with `sqlite3` and POSIX `fcntl`; training requires Apple
silicon macOS, a working PyTorch MPS build, and NumPy. Install compatible Torch
and NumPy packages in the interpreter's normal environment before use. Tested
locally with Python 3.9.6, Torch 2.8.0 and NumPy 2.0.2. No dependency manager is
required. CPU checks need Torch and NumPy; history queries need neither.
Use `-B`, not `-I`: an isolated interpreter hides user-site Torch installations.

From the repository root:

```sh
PYTHON=/Applications/Xcode.app/Contents/Developer/usr/bin/python3
TOOL=tools/scripts/agent/gpu5040
STATE="$HOME/.local/state/gpu5040/state"
HISTORY="$HOME/.local/state/gpu5040/history.sqlite3"
export PYTORCH_ENABLE_MPS_FALLBACK=0
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
```

The shared default is `${XDG_STATE_HOME:-$HOME/.local/state}/gpu5040`, containing
`history.sqlite3`, `gpu-verifier.lock`, and the default `state/`. `--state-dir`
does not change the default registry or GPU lock. `--history-db` selects explicit
independent knowledge; it does not permit concurrent GPU use. Resume retains the
checkpoint's recorded registry path and rejects a conflicting path.
`GPU5040_SHARED_ROOT` relocates the common root; every source copy on the same
machine must use the same value. These are local filesystem locks, not leases,
a distributed scheduler, or coordination with pre-registry workers.

All checkpoints, status, logs, locks and databases must remain outside source
directories and repository trees. Locks acquire the canonical state path first,
then the shared GPU/verifier lock, nonblocking. Never delete a lock file to unlock
it. A stopped process releases `fcntl` locks automatically.

## Run and Inspect

```sh
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$STATE" --history-db "$HISTORY" \
  --dimensions 13,16 --seed-steps 100 --batch-steps 5 --max-steps 100
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$STATE" --resume --max-steps 100
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$STATE" --fresh-start --max-steps 100
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$STATE" --status
"$PYTHON" -B "$TOOL/trial_history.py" --history-db "$HISTORY" --status completed --limit 100
"$PYTHON" -B "$TOOL/trial_history.py" --history-db "$HISTORY" --dimension 13
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$STATE" --verify 13
```

`--max-steps` counts additional optimizer updates, never skipped trials.
`--max-seconds` is a soft invocation bound checked at boundaries and while
skipping. The full per-trial budget is `--seed-steps`, independent of invocation
bounds. `--forever` explicitly enables an unbounded foreground traversal.
Existing checkpoints auto-resume; `--resume` requires one. `--fresh-start`
inherits saved configuration unless overridden and begins a new traversal,
retaining the database and dimension bests. An unfinished checkpoint rejects
fresh-start with a `--resume` instruction; finish it with its original scientific
configuration and numerical runtime first.

The random-v1 identity contains the physical model, actual dimension/seed, initialization,
all Adam settings, cosine schedule, full update budget, algorithm version,
float32 dtype and numerical runtime. NumPy's version belongs to verification
provenance, since the optimizer does not call NumPy. Random identity excludes source hashes, executable and
state paths, invocation limits, logging/checkpoint cadence, verification trigger
settings and the MPS memory fraction. The source never feeds these operational
values or champion tensors into an optimizer update. Source/config hashes remain
provenance. Resume still rejects an actual scientific source hash mismatch;
retaining the random descriptor does not make different source bytes equivalent.
Scientific code changes require an algorithm version change; checkpoint layout
compatibility uses a separate schema version.

## Analytic D55 Input

`--initializer analytic-d55` selects one deterministic candidate with dimensions
`[55]`. The complete declarative recipe lives in
`Evidence/D5/S3/Quantum/AnalyticD55Initializer.result.json`; an exact relocated
copy can be supplied with `--initializer-recipe PATH`. Content is validated before
claim or tensor allocation. Changed content is rejected by this baseline version.
Raw input bytes and their path/hash are checkpoint provenance; the complete typed
recipe, orientation, positive-target converter version, actual six-file scientific
source hash, precision, runtime and Adam budget enter the analytic trial identity.

The constructor uses physical completion-count square roots, the specified
`40/41,9/41` column rotation and positive initial weights. Positive-target
Householder reduction stores reversed reflector rows over the existing fixed eye
basis. Raw Gram and vector norms and entrywise reconstruction must pass before
training. The model retains exactly the `reflectors` and `initial` parameters;
the eye basis is nonpersistent. Checkpoint schema 2 and numeric Config fields are
unchanged. The initial vector remains trainable and normalized by forward.

The analytic effective seed is always 0, with explicit RNG reset and zero
initializer draws. A requested base seed is retained as provenance and creates
no additional exploration. `--forever` is rejected. Completed content skips
before allocation and stops as `exhausted`, including when `--max-steps` alone
is given or the final update coincides with that bound. A skip records zero
updates. An empty state can be exhausted without `latest.pt`; a fresh traversal
retains an older real checkpoint under a separate status receipt.

For a fresh, isolated CPU verification state and history:

```sh
ANALYTIC_STATE="$HOME/.local/state/gpu5040/analytic-cpu-verification"
ANALYTIC_HISTORY="$HOME/.local/state/gpu5040/analytic-cpu-verification.sqlite3"
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$ANALYTIC_STATE" \
  --history-db "$ANALYTIC_HISTORY" --initializer analytic-d55 \
  --device cpu --precision float64 --seed-steps 6 --batch-steps 1 --max-steps 3
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$ANALYTIC_STATE" \
  --resume --device cpu --precision float64 --max-steps 3
```

CPU training requires the analytic protocol and explicit `--device cpu`.
MPS uses float32 and requires a separately authorized root handoff. No automatic
device choice or CPU fallback occurs. On resume, the worker allocates only the
fixed model layout, restores saved parameters, Adam and selected-device RNG, and
records the first forward in `startup.json` before updates. It never regenerates
initializer tensors on that path; a recipe path is unnecessary for resume.
CPU checkpoints retain the RNG envelope with `torch_mps: null`, explicitly
inapplicable; actual MPS checkpoints retain CPU and MPS RNG byte tensors.

Only exact completed optimization identities, or explicitly selected legacy
lineage exclusions, are skipped before model initialization. Interrupted and
failed claims remain unfinished; another state cannot steal them. Retry in the
recorded state with the same configuration, using `--resume` when it has a
checkpoint. History status is the last recorded state, not a process-liveness
probe; startup reconciles recoverable checkpoints before selection or fresh-start.

History stores one compact row per trial, including initial/final/best scalar
metrics and iterations. Dimension champions and candidate-digest CPU verification
records are separate. Verification is finite-precision evidence and is not a
condition for completed optimization. No per-step rows or per-trial tensors are
retained: state keeps `latest.pt`, at most one `best-D.pt` per dimension, and
bounded rotating logs. Champion paths can become unavailable if external state
is removed; a digest is not a retained tensor. The scalar database grows with
completed trials and should be retained/backed up while workers are stopped.

Terminal checkpoint publication fsyncs the file and directory before SQLite's
completion transaction (`synchronous=EXTRA`, rollback journal). A failed commit
leaves terminal recovery evidence intact; restart reconciles it idempotently.
Completed rows survive subsequent replacement of `latest.pt`. After a crash,
resume the worker directly to repair status before restarting the launcher.

## Pause and Repetition

```sh
touch "$STATE/STOP"
# Alternatively send SIGTERM or SIGINT to the owned foreground worker/launcher.
# After its graceful exit, remove only the STOP sentinel to allow another run:
rm "$STATE/STOP"
"$PYTHON" -B "$TOOL/gpu_bounded_launcher.py" --state-dir "$STATE" --history-db "$HISTORY"
```

For random trials the launcher runs one additional round of actual updates, deriving its budget
from saved dimensions and seed steps. Exit 0 requests existing launchd
`SuccessfulExit` repetition only after exact additional-update and fresh durable
checkpoint validation, bound to child PID, invocation UUID, progress and digest.
STOP, signals, failures, stale receipts and malformed status exit nonzero.
Signals are forwarded and the child is joined. This tool installs no service.
Analytic trials run only the remaining singleton budget. Validated exhaustion
returns **exit 4**, which never requests repetition, including an already
exhausted state that launches no child. The launcher validates analytic content
identity, source, invocation, progress and checkpoint digest; a zero-update skip
is never an exact-budget work receipt. It propagates the saved explicit device
and precision. Changed scientific source bytes require their own scientific
run; old checkpoints cannot be relabeled by a resume invocation.

## Legacy Conversion

Pause the old worker and retain a separate stopped snapshot containing its exact
`gpu_worker.py`, `tensor_core.py`, original `PREREGISTRATION.md`, `latest.pt`, and
all `best-*.pt`. Old source-local locks cannot coordinate with the new shared
lock: root must quiesce the old service before any new MPS run. Keep the original
source/state and preregistration unchanged externally for recovery and provenance.

The converter requires `stopped.json` in that snapshot, supplied by its owner
after graceful exit. Its fields are `stopped: true`, `source_sha256` (SHA-256 of
worker name, NUL, worker bytes, core name, NUL, core bytes), `checkpoint_sha256`,
and `best_sha256` (a map of every retained best filename to its SHA-256).
The supported source hash is
`e2e66992c9e5209c8b37ccc3cae809d40764eee579b83e13e82a13833d284eb5`.
This marker attests snapshot acquisition; it cannot itself prove a process stopped.

```sh
SNAPSHOT="$HOME/.local/share/trureturing-research/gpu5040/retained-stopped-snapshot"
MIGRATED="$HOME/.local/state/gpu5040/migrated"
"$PYTHON" -B "$TOOL/legacy_conversion.py" --snapshot "$SNAPSHOT" \
  --state-dir "$MIGRATED" --history-db "$HISTORY"
"$PYTHON" -B "$TOOL/trial_history.py" --history-db "$HISTORY"
"$PYTHON" -B "$TOOL/gpu_worker.py" --state-dir "$MIGRATED" --resume --max-steps 1
```

Conversion validates known source, physical/configuration compatibility, exact
snapshot digests, schedule continuity, tensor shapes/dtypes and Adam state. It
preserves current parameters, optimizer, CPU/MPS RNG and dimension best tensors.
New converted latest checkpoints bind the current six-file source closure;
the exact historical source hash remains in migration evidence. Migration
metadata cannot bypass the worker's actual source check. Existing outputs are
never rewritten merely to update a source hash.
Retained champions and available verification results enter separate history
tables under the checked candidate digest; missing verifier provenance stays unknown.
It imports indices below `run_index`, and the current index only when
`iteration == seed_steps`. It infers nothing before the last fresh-start.
Missing prefix metrics/runtime are null; current legacy best metrics are marked
incomplete, not replaced with the dimension champion. Repeating the conversion
is idempotent and never resets later progress in its output state.

Unknown legacy runtime cannot define an exact modern identity. The conversion
returns a `lineage`; migrated resumes/fresh traversals retain it automatically.
A new state joins it only with `--legacy-lineage LINEAGE`. Exclusions compare
all known scientific fields within that explicit lineage. Independent campaigns
never match an unknown-field wildcard. Unrecorded legacy runtime fields remain
unknown even when the current tensors can be resumed.

Root should inspect conversion counts, run independent review and bounded MPS
checks, then point the existing service at the repo worker/launcher and migrated
external state. Repository publication, required checks and deployment are root's
operations; this implementation does not perform them.

## Local Checks

```sh
"$PYTHON" -B -m unittest discover -s "$TOOL" -p 'test_*.py' -v
"$PYTHON" -B "$TOOL/smoke_test.py"          # CPU numerical checks only
"$PYTHON" -B "$TOOL/smoke_test.py" --mps    # root only, after pausing old GPU work
```

Tests use external temporary state, fault injection and pipe barriers;
timeouts are infrastructure hang guards, not performance assertions. The MPS
smoke additionally compares resumed/continuous parameters, Adam moments and RNG,
and checks deduplication, CPU verification and launcher accounting. These Python
tests are local checks; existing ScriptTests are excluded from CI, and required
repository CI is not claimed to run this suite.

`test_analytic_initializer.py` checks physical bytes, both CPU precisions,
chronological full-word amplitudes and the baseline, signed-phase, invalid Gram,
rational-gauge and D56 controls. `test_analytic_resume.py` runs actual D55 Adam
for six updates versus three plus a durable new-process reload plus three. It
compares saved/loaded bytes, the first restored forward, each trajectory step,
final parameters/moments/RNG, exact counters/LR and trained best restoration.
Its CPU subprocesses guard accelerator APIs. Set `GPU5040_ADAM_EVIDENCE` to a
fresh external directory to retain raw observations, checkpoint bytes, commands
and readings. `GPU5040_NUMERICAL_EVIDENCE` similarly retains precision evidence.
The MPS persistence test is skipped unless root explicitly sets
`GPU5040_RUN_MPS=1` after its serialized handoff. CPU results do not discharge
actual MPS precision/persistence, independent review, required CI, MERGED
delivery or termination obligations.
