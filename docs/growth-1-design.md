# Growth-1 Capacity Design

Status: implementation design record, not a normative repository specification.
The normative contract remains `docs/develop/spec/golden-ledger-repo-spec.md`.

## Goal

Increase monthly harness capacity without weakening admission semantics:

- identify reclaimable lane worktrees, stale gate judge trees, and orphaned
  `harness/*` branches, with dry-run as the default and mutation only under an
  explicit force flag;
- produce candidate and baseline Lean reports once when their complete report
  inputs are content-equivalent, while retaining auditable provenance;
- avoid repeating candidate engineering checks inside `make preflight`; and
- append machine-readable stage timing to every local gate run.

The growth-audit source artifacts named in the task were no longer present in
the accessible filesystem or Git history at implementation time. The retained
measurements supplied with the task are therefore the evidence boundary: 11
discarded worktrees represented 108 GiB of logical data, and each redundant
Lean inspection cost about 192 seconds while frequently producing identical
SHA-256 reports.

## Approaches Considered

### 1. Shell-only orchestration

A single Bash script could parse `git worktree` output, remove directories, hash
Lean inputs, and print timings. This is compact, but makes concurrent branch
movement, path validation, JSON emission, and deletion testing unnecessarily
fragile.

### 2. Report-SHA reuse after both inspections

The gate could compare output SHA-256 values and retain only one report. This is
auditable but saves no inspection time, so it does not address the measured
bottleneck.

### 3. Typed cleanup plus content-addressed report pairing (selected)

The existing C# CLI owns worktree classification and mutation. A narrow shell
adapter keeps `make clean-lanes` a one-recipe dispatch target. A separate report
pair helper computes both input addresses before invoking the base-owned Lean
producer, and the local/shared gate scripts exchange timing through one timing
file. This gives the destructive path typed tests and lets report production
remain a native Lean predecessor stage.

## Clean-Lanes Contract

The command resolves a supplied base revision, enumerates registered worktrees
and managed local branches, and emits JSON Lines records in stable order.
Managed lane branches are `harness/*` and `agent/<official>/<task-code>`.

A registered lane worktree is eligible only when all of these predicates hold:

1. it is not the command's current repository root;
2. its branch tip is an ancestor of the resolved dev base;
3. `git status --porcelain -z` is empty, including untracked files; and
4. its observed branch and tip still match immediately before mutation.

`/tmp/trureturing-*` judge remnants are eligible only when they are detached or
unregistered and their Git administrative pointer resolves under the same
common Git directory. Symlinks and attached branches are rejected. An orphaned
managed branch is eligible only when no worktree owns it and its exact tip is an
ancestor of the base.

Dry-run emits `would_remove`; `--force` removes eligible worktrees and uses
`git update-ref -d <ref> <observed-tip>` so a concurrent ref movement fails
closed. Dirty, unmerged, current, foreign, and ambiguous items are reported but
never removed. The command never deletes remote refs.

## Lean Report Reuse Contract

The pair helper receives one base-owned producer and two repository roots. For
each side it computes a canonical input preimage containing:

- SHA-256 of the invoked `inspect.sh` and its `Inspector.lean`;
- SHA-256 of the relative-path-and-content manifest for `Trureturing.lean` and
  every `D5/**/*.lean` source;
- SHA-256 of `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`; and
- a versioned input-address schema.

Only byte-equal input addresses permit reuse. On equality the candidate report
is produced normally, copied byte-for-byte to the baseline output, and checked
against a newly written SHA-256 sidecar. On any missing input, malformed output,
or address mismatch, the helper fails closed or runs the producer independently
for both sides exactly as before.

Each side receives a JSON provenance attestation with its input address, report
SHA-256, production mode (`produced` or `reused`), and source side. CI uploads
these files with the raw reports; local gate output repeats the provenance event
so a captured gate log remains auditable after temporary files are cleaned.

## Gate Flow And Timing

`local-harness-gate.sh` accepts `--skip-engineering`. Its default behavior is
unchanged. `preflight.sh` runs restore, candidate dotnet/test/selftest, and both
compile-fail proofs, then explicitly invokes the gate with that flag. No
validation step disappears; the already completed engineering stages have one
canonical owner in preflight.

Local stages and nested shared-gate stages append JSON Lines timing records to a
temporary file. `STRATALINT_TIMING` is redefined as the absolute timing-file
contract and consumed by `.github/scripts/harness-gate.sh`; it is no longer an
unused boolean. The local EXIT trap preserves the gate status, cleans temporary
state, and prints all records followed by one total/status JSON record as the
tail of stdout/stderr, including on failure.

## Verification

Tests cover dry-run immutability, force deletion of a clean merged lane,
protection of dirty/unmerged/current worktrees, orphan cleanup, foreign temp
directory rejection, report reuse on equal addresses, double production on a
single source/config/producer mismatch, provenance bytes, explicit preflight
skip wiring, timing-file consumption, and Makefile thin dispatch. Full
acceptance remains `make preflight BASE=origin/dev` followed by a clean-tree and
remote-branch identity check.
