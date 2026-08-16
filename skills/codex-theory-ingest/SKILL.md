---
name: codex-theory-ingest
description: Use when adding a new externally authored theory document to trureturing and carrying it through canonical digestion into open formalization atoms.
---

# Codex Theory Ingest Workflow

## Install

This is a Codex skill package. Install it by copying the
`skills/codex-theory-ingest/` directory into `$CODEX_HOME/skills/` (default
`~/.codex/skills`), or load it by naming this `SKILL.md` path directly in a
dispatcher. This repository copy is the single source of truth; any installed
copy is a projection of it.

## Scope and authority

This file is Codex-specific packaging of repository obligations; it has no
authority of its own. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole
normative specification; `CLAUDE.md` is the invariant frame governing how work
is done; and `agents/CONTEXT.md` is the finite-context map and routing aid, not
an authority above the specification. Live harness output is the decisive judge
of fact about the current tree. If this file disagrees with any of them, they win
and this file is the bug.

## Read first

- `CLAUDE.md` - owns the invariant frame, including reference-input status,
  no-overclaim, worktree isolation, TDD, and machine-only gates.
- `agents/CONTEXT.md` - owns the finite-context map and routing guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md` - owns the normative repository
  specification; read the current A16.1 text in full before acting.
- `Meta/registry.yaml` - owns the current canonical governance-document list.
- `skills/codex-formalize/SKILL.md` - owns the downstream open-atom workflow.
- `make help` - owns the live catalogue of canonical doors.
- `tools/StrataLint.Engine/Digestion/DigestionIngestor.cs` - owns default source
  discovery and source-id derivation.
- `tools/StrataLint.Engine/Digestion/Atomizers/GenericAtomizer.cs` and
  `tools/StrataLint.Cli/Commands/DigestStatusCommand.cs` - own generic claim
  recognition and formalization-candidate eligibility.

## State machine

Follow these steps in order. Do not pass a step until its postcondition holds.

Unless a step names a bounded recovery, every command result has exactly one
successor: exit 0 with the stated postcondition satisfied advances to the next
step; any nonzero exit or unmet postcondition ends in evidence-complete `open`.
Likewise, every pull request has exactly one terminal successor: `MERGED`
advances or completes the workflow, while any terminal non-merged state ends in
evidence-complete `open`. There are no implicit retries.

Every such `open` report must identify the step, reproduce the exact command,
record its exit code or external terminal state and machine diagnostic, name the
branch, and include the complete `git status --short` tree state. Preserve every
canonical-writer output and the resulting tree exactly as found: do not hand-fix,
delete, reset, or clean generated artifacts to make the failure look tidy.

### 0. Establish isolation

Run:

```sh
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
# If no dispatcher-assigned isolated lane exists:
make worktree NAME=<lane> && cd <created-path-from-output>
pwd -P && git rev-parse --show-toplevel && git status --short
```

If already assigned an isolated lane, do not create a nested worktree. Confirm
that `pwd -P` equals `git rev-parse --show-toplevel`, the branch is not `dev`, and
the status contains no unrelated change. Run all later commands only there.

Postcondition: the task has one isolated, identified worktree and a clean or
fully explained starting status.

### 1. Accept and classify the source

Require both inputs:

1. One theory document, supplied as a path or as complete text.
2. Provenance containing author kind (`human`, `AI`, or `mixed`), author/model,
   source or session identifier, and date. Record an AI author as AI; do not
   substitute a human name or lower the work's status merely because it is AI
   authored.

Classify the document by its substance. Proceed only for mathematical or
methodological exposition whose claims are intended as reference input. A Lean
module, executable program, experiment dataset, evidence record, repository
policy, or governance specification is not a theory volume: route it through
the live `agents/CONTEXT.md` manifest/owner path instead of placing it under
`docs/develop/theory/`. Reject an edit to an existing theory volume as outside
this add-only workflow.

Postcondition: the input is a new theory reference document, its complete
provenance is available, and no existing volume will be changed.

### 2. Normalize without changing meaning

Apply this authoring contract:

- Choose a descriptive ASCII `.md` filename in the existing uppercase volume
  style, using `_` or `-` between terms, for example `NEW_THEORY_VOLUME.md`.
  The default source id is the filename stem lowercased with each run of
  non-alphanumeric characters collapsed to `-`; reject a collision with any
  existing source id before landing the file.
- Start with one H1 title and include the Step 1 provenance in the document.
  Mark the document as reference input and state that Lean, not this prose, is
  the repository truth source.
- Put every claim intended for formalization under a numbered heading whose
  leading kind is exactly one of lowercase `theorem`, `proposition`, `lemma`, or
  `corollary`, followed by a decimal or dotted number. For example:

  ```md
  ## theorem 1.1: Descriptive title

  **Claim status: open.** <the claim, with its domains, hypotheses, and conclusion>
  ```

  `generic-v1` preserves the kind token verbatim, while
  `digest-status --formalize-candidates` accepts exactly those four lowercase
  tokens. Uppercase or translated kinds still digest, but do not enter that
  queue.
- Give unverified claims explicit `open` or `conjecture` language. A source may
  faithfully say that it contains a paper argument, but it must not say
  `Lean-verified`, `closed`, `frozen`, or equivalent unless the current ledger
  supplies that receipt.
- Treat theory and claim numbers only as local provenance. Never derive a Lean
  name, GID, dependency, or structural address from them.
- Preserve every authorial claim sentence. Structural normalization may add
  headings and provenance labels; it may not weaken, strengthen, split, merge,
  or rewrite a claim merely to make atomization succeed. If claim boundaries
  cannot be identified without interpreting or changing the source, stop with
  an evidence-complete `open` that names the ambiguity.

Postcondition: the normalized bytes retain the author's meaning, provenance and
truth status are explicit, and at least one intended formalization claim has an
eligible numbered lowercase heading.

### 3. Register first, then land the volume

Read A16.1 again from the current specification. Its current obligation is two
ordered pull requests even while its former machine enforcement is deferred.

**Registration PR:** On a dedicated branch, add only the future volume path to
`Meta/registry.yaml` under `governance_documents`, preserving canonical ordering.
Do not add the volume or digestion data. Commit, run `make preflight`, push, and
run `make pr-open`; every command must exit 0. After `make pr-open`, do not push
further changes to that branch. Poll until the PR is `MERGED` or reaches a
terminal non-merged state. Only `MERGED` advances to the theory PR; a command
failure or terminal non-merged state takes the global `open` transition with the
retained registration branch, exact command and exit code or PR state, machine
diagnostic, and tree state. A green or merely open PR is not a postcondition. If
the exact path is already present in the protected base, prove that fact from
`origin/dev` and do not create a duplicate registration PR.

**Theory PR:** After registration is merged, create a fresh worktree from the
new `origin/dev`. Confirm that its registry already contains the path, then add
only `docs/develop/theory/<filename>.md`. The theory branch must contain no
registry diff.

Postcondition: the protected base pre-registers the exact path, and the fresh
theory branch contains one new normalized volume with no edit to an existing
volume or to `Meta/registry.yaml`.

### 4. Ingest and verify the new atoms

Record `git status --short`, then run the canonical writer:

```sh
make ingest
```

Require exit 0, `coarse_fallbacks=0`, `ledger_changed=true`, and
`residual_open_added` greater than zero. There is one named recovery. If, and
only if, `make ingest` exits 2 and its output contains one of these canonical
report-prerequisite diagnostics (where `<path>` is the path emitted by the
machine):

- `report-consumer: raw Lean report is missing at <path>; run make lean-report first`
- `report-consumer: raw Lean report bundle is incomplete at <path>; run make lean-report first`
- `report-consumer: consumption failed; the raw Lean report may be stale, run make lean-report first`

run `make lean-report` exactly once, require exit 0, then retry `make ingest`
exactly once. The retry must itself exit 0 and satisfy every ingest postcondition
above. A nonzero `make lean-report`, any failed retry, or an exit 2 without one of
the three diagnostics takes the global `open` transition. Never treat an
arbitrary exit 2 as a report prerequisite and never attempt a second recovery.

Do not create or edit any `Meta/Digestion/**` file yourself. Locate the one
generated `Meta/Digestion/backfill/<source_id>/source.toml` whose `path` equals
the new volume, and require its `atomizer` to be `generic-v1`. Locate at least
one generated `residual-open/*.yaml` whose `ast_path` begins with an eligible
kind, derive its atom id from the filename, then run:

```sh
make show-atom ATOM_ID=<atom-id>
```

Require exit 0, `HASH_VERIFY ... status=match`, the expected source path and
source id, and raw text faithful to the corresponding source claim.

Use the live CLI to verify both the ledger and downstream queue:

```sh
theory_ingest_tmp="$(mktemp -d)"
dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release -- digest-status --json --base origin/dev \
  > "$theory_ingest_tmp/status.json"
dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release -- digest-status --formalize-candidates --base origin/dev \
  > "$theory_ingest_tmp/candidates.json"
jq -e --arg source_id '<source-id>' \
  '[.entries[] | select(.source_id == $source_id and .migration == "residual" and .truth == "open")] | length > 0' \
  "$theory_ingest_tmp/status.json"
jq -e --arg source_id '<source-id>' --arg atom_id '<atom-id>' \
  '[.candidates[] | select(.source_id == $source_id and .atom_id == $atom_id)] | length == 1' \
  "$theory_ingest_tmp/candidates.json"
```

Every command must exit 0. The filtered residual count is the source-scoped
residual increment; record it and the candidate atom ids rather than counting or
editing ledger entries by hand.

Postcondition: canonical ingest created the source record and CAS-backed atoms,
`show-atom` reads at least one eligible claim back with matching hashes, and the
same atom appears exactly once in the formalization-candidate output.

### 5. Preflight, publish, and wait for the machine verdict

Review `git diff` and require every `Meta/Digestion/**` change to be an output of
the successful Step 4 writer. Prepare a pull-request body that records:

- provenance and the new volume path;
- source id, residual increment, and eligible atom ids;
- every verification command and exit code, including any report-prerequisite recovery;
- the exact `show-atom` hash-match evidence.

Commit the theory volume and writer-produced digestion data, then run:

```sh
make preflight BASE=$(git merge-base origin/dev HEAD)
git push -u origin <branch>
make pr-open HEAD=<branch> TITLE='<title>' BODY=<body-file>
```

Require preflight and both publication commands to exit 0. Do not push further
changes after `make pr-open`; a follow-up requires a new branch. Poll the PR's
machine state until it is `MERGED` or reaches a terminal non-merged state.
Report completion only for `MERGED`. Otherwise report evidence-complete `open`
with the terminal state, failed command or check, exit code, and retained branch.
Never introduce a human-review waiting state.

Postcondition: the theory PR is `MERGED`, or the run ends honestly as
evidence-complete `open`. Downstream formalization begins by invoking
`skills/codex-formalize/SKILL.md` on one of the emitted open atoms; this skill
does not perform that work.

## Prohibitions

- Never hand-edit `Meta/Digestion/**`; `make ingest` is its exclusive writer.
- Never modify an existing theory volume in this add-only workflow.
- Never fabricate, conceal, or reassign provenance.
- Never change claim semantics to obtain a preferred atom boundary or kind.
- Never present prose, a paper proof, or AI confidence as Lean-verified truth.
- Never bind Lean structure to theory numbering.
- Never add an atomizer, ingestion command, compatibility path, or parallel
  ledger for one volume. Reuse `generic-v1`; price new harness only after actual
  repeated pressure establishes a new class.
- Never use a human-review requirement as a gate or terminal state.

## What this skill does not own

- Repository policy and the two-PR registration obligation are owned by the
  specification and `Meta/registry.yaml` consumers.
- Source discovery, source-id derivation, atom boundaries, CAS writes, and
  digestion status are owned by the live ingestion engine and canonical doors.
- Claim truth, Lean declarations, freezing, coverage, and receipts are owned by
  Lean, `skills/codex-formalize`, and the deposit/cover doors.
- Routing for non-theory inputs is owned by `agents/CONTEXT.md` and the live
  route harness.
- Authorial substance and provenance remain the source author's; normalization
  grants this skill no editorial or truth authority.

This skill names each concern's owner without reproducing its changing
thresholds. Discover current facts from those owners; the harness is the judge.
