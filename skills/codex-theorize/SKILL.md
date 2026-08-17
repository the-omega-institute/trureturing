---
name: codex-theorize
description: Use when researching an open mathematical question with repository knowledge and producing an honest, machine-admissible theorem candidate in D5/X_Frontier.
---

# Codex Theory Generation Workflow

## Install

This is a Codex skill package. Install it by copying the
`skills/codex-theorize/` directory into `$CODEX_HOME/skills/` (default
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

This workflow accepts only a P1 candidate whose `downstream_lane` is
`theorist`. It applies the repository's own method: establish coordinates from
frozen GIDs, classify the question and its possible falsifier, take source and
computational readings, and keep a receipt for every load-bearing move. Its only
repository result is an honest open Lean declaration in `D5/X_Frontier/` that
satisfies the P2 contract. It does not prove or freeze that declaration.

## Read first

- `CLAUDE.md` - owns the invariant frame, including Lean-only truth,
  no-overclaim, library-before-proof, worktree isolation, TDD, and machine-only
  gates.
- `agents/CONTEXT.md` - owns the finite-context map and routing guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md` - owns the normative repository
  specification; read current sections 11.20.1 and 11.20.2 in full.
- `docs/MISSION.md` - owns the typed Frontier eligibility and current selection
  policy. An open WorthVector permits only `bootstrap eligibility order`, never
  a claimed worth score or argmax.
- `agents/theorist.md` - owns the theorist role and its six-part output.
- `agents/echo-template.md` - owns the statement echo.
- `make help` - owns the live catalogue of canonical doors.
- `tools/StrataLint.Engine/Rules/TheoryGeneration/TheoristFrontierContractValidator.cs`
  - owns the live P2 validation details.
- `skills/codex-formalize/SKILL.md` - owns residual-atom formalization; it is a
  downstream boundary, not a subroutine of this workflow.
- `skills/codex-theory-ingest/SKILL.md` - owns the family-wide bounded REST
  pull-request observation protocol reused in Step 8.

## State machine

Follow these steps in order. Do not pass a step until its postcondition holds.
Run commands bare and judge them by their own exit codes, not by piped output.
Retain exact commands, stdout, stderr, exit codes, artifact paths, and SHA-256
addresses in a run-local log outside the worktree. A nonzero command or unmet
postcondition ends in the evidence-complete `open` terminal unless the step
explicitly names a repair followed by a fresh execution of that same gate.

There are exactly two terminal states:

- `success`: the pull request is REST-confirmed `MERGED`, its merge commit and
  target declaration GID are named, and every Step 1-7 postcondition is
  evidenced;
- `open`: the stopping step and named gap are recorded together with every
  artifact and machine diagnostic reached so far. Existing-result reuse,
  missing evidence, a wall, and infrastructure failure are all honest `open`
  outcomes, not failures to be hidden.

Every terminal report carries these fields without inventing a truth status:

```text
terminal
stopping_step
candidate_id
candidate_content_sha256
selection_mode
selection_receipt
problem_echo
motivation_gids
target_gid
exact_statement_sha256
falsifier
search_queries
search_receipt_gids
computation_summary
computation_receipt_gids
triage_class
adversarial_result
commands_and_exit_codes
changed_paths
git_status_porcelain
commit_sha
resolved_base_sha
preflight_exit_code
pr_number
pr_state
merged_at
merge_commit_sha
landed_dev_sha
named_gap
command_log_path
```

Use `null` plus a reason in `named_gap` for fields not reached. Never fill a
field with an inference that its owner did not issue.

### 0. Establish isolation

Run:

```sh
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
# If no dispatcher-assigned isolated lane exists:
make worktree NAME=<lane> && cd <created-path-from-output>
pwd -P && git rev-parse --show-toplevel && git status --short
make -C tools dotnet
```

If already assigned an isolated lane, do not create a nested worktree. Confirm
that `pwd -P` equals `git rev-parse --show-toplevel`, the branch is not `dev`,
and every starting change is explained. Re-read the PATH export from the live
script; do not paste a remembered PATH.

Postcondition: one isolated worktree is identified, the Release CLI is built,
and no unrelated or unexplained change is present.

### 1. Select one machine-issued theorist candidate

Run exactly one of:

```sh
make theory-candidates
make theory-candidates OWNER_OVERRIDE_FILE=/absolute/path/to/strict-utf8-question.txt
```

Capture stdout without editing or normalizing it. Select only the candidate
named by `selection_receipt.selected_candidate_id`; do not rescore, reorder, or
skip to a later candidate. With no override, the producer owns bootstrap
ordering. With an owner override, require
`selection_mode="owner_override"` and retain the raw-file content address.

Require the selected candidate to exist and have
`downstream_lane="theorist"`. A selected `prover` or `codex-formalize`
candidate belongs to that lane and ends this run `open`; it is not permission to
reinterpret the item. Natural-language problem text must never be sent directly
to a prover.

Branch on `source_kind`. An `owner_override` must carry the exact nonblank
`problem_text` decoded from the address-bound override bytes. A repository
`frontier_problem` carries `problem_text=null` by P1 design: retain that null,
read the exact `<source_ref>.lean` bytes, confirm their SHA-256 equals the P1
`content_sha256`, and quote the owner-issued mathematical request from those
bytes without using a TASK number to infer its semantic class. Any other shape
ends `open` with the mismatch named.

Postcondition: the unmodified P1 selection receipt, selected candidate ID,
content address, source reference, source kind, nullable P1 problem text, exact
question input bytes, and `theorist` lane are recorded.

### 2. Ground and echo the question

Apply `agents/echo-template.md` to the selected problem. Name its objects,
domains, quantifiers, assumptions, desired conclusion, ambiguity set, and a
concrete observation that would falsify it. Classify the intended result as
exactly one of `theorem`, `window`, or `wall`.

Search the current formal DAG and propose a nonempty, ordinal-sorted, unique
`motivation_gids` list. Each item must resolve to a Formal-plane module or
declaration whose module is an active member of `Golden/Frozen/accepted/`.
File existence, prose mention, or a revoked historical event is not enough.

If the natural-language question cannot be mapped to one exact proposition
without silently weakening or strengthening it, end `open` and name the
ambiguity. Do not hard-code prose into a vacuous Lean predicate merely to obtain
a declaration.

Postcondition: the statement echo is clause-complete; the falsifier and triage
class are explicit; and every proposed motivation GID has an active frozen
anchor.

### 3. Search before generating

Search, in order, the active frozen declarations under `D5/`, pinned mathlib,
repository `Library/`, and relevant external literature when available. Record
each query verbatim, its scope, and its result. Search both conclusion and
hypothesis shapes; a stronger existing theorem is an exact hit even when its
name differs.

Every source actually relied on must have a canonical, existing Library-plane
receipt GID `D5/L/...`. The final list must be nonempty, ordinal-sorted, and
unique. If an external source is load-bearing but has no existing repository
Library receipt, end `open` and name that missing receipt. Do not create or edit
a source receipt in this lane, and do not cite an unrecorded URL or model
recollection as a receipt.

An equal or stronger existing theorem ends this run evidence-complete `open`
with a bind/reuse recommendation naming the hit and its frozen address. Do not
manufacture a renamed wrapper or a `sorry` version of known truth. A search that
cannot be completed faithfully also ends `open` with the missing search named.

Postcondition: duplicate search is complete, all load-bearing sources resolve
to Library receipt GIDs, and no equal or stronger existing result was found.

### 4. Calculate at least one reading

Perform at least one computation that can expose a false conjecture, constrain
the exact statement, or distinguish `theorem`, `window`, and `wall`. Examples
include a finite counterexample search, symbolic reduction, exact arithmetic,
or a checked Lean evaluation. Record inputs, executable method, output, and the
interpretation separately; computation is evidence, not proof.

The computation must resolve to a canonical existing Evidence-plane receipt
GID `D5/E/...--<kind>`. If no suitable receipt exists, end `open` and name that
missing receipt. Do not create or edit an Evidence receipt in this lane, and do
not place data in code, comments, `Meta/`, or an ad hoc transcript. The final
list must be nonempty, ordinal-sorted, and unique.

The machine handoff owner for that missing receipt is `numericist`, whose
charter permits Evidence writes. Record the exact calculation specification and
required receipt kind in the `open` terminal. Only after a numericist PR returns
the canonical Evidence GID and is REST-confirmed `MERGED` may a new
`codex-theorize` run select the problem again; do not resurrect this terminal
run or treat the handoff as success.

If no relevant computation is possible, end `open` and name why, including the
missing data or executable specification. A prose claim that calculation would
be unhelpful does not discharge this step.

Postcondition: at least one reproducible calculation and one resolving
computation receipt GID are recorded, and the statement/triage consequences are
explicit.

### 5. State exactly one open Lean declaration

For `source_kind="frontier_problem"`, the only natural owner is the P1
`source_ref`; edit that existing module and no other. For
`source_kind="owner_override"`, the content address is not a Frontier owner:
construct the strict manifest for the intended D5 `X_Frontier` module and run
the repository's canonical route command. Proceed only when canonical route
returns one `D5/X_Frontier/<Target>` GID and path; a route rejection, capacity
finding, or non-Frontier result ends `open` without inventing an address.

Create or transform only that machine-returned natural owner. Add or update the
same module's `docs/MISSION.md.frontier_eligibility` entry to
`declaration-ready-mathematical-open`; never infer eligibility from TASK text,
path, name, or `sorry`. The module must elaborate and contain exactly one
`include_in_statement=true` declaration whose compiled axiom closure contains
`sorryAx`. Use `by sorry`; never use an `axiom` or a self-reported status.

Echo every source clause into the exact Lean statement and check that the
falsifier still negates that exact statement. The proposition must not be
`True`, a restatement of a hypothesis, a definition installed to make itself
true, a weaker duplicate, or a classifier invented solely to make the theorem
hold.

If the only semantically valid reusable owner is an attested input of an
existing generated receipt and changing that owner makes admission require the
receipt to be regenerated, end `open`. Name the owner-to-receipt coupling and
the machine diagnostic; do not expand this lane's write authority to make the
candidate pass.

Embed exactly one current P2 contract block in the source. Copy its field names
and delimiters from section 11.20.2 rather than memory:

```lean
/- THEORIST_FRONTIER_CONTRACT_V1
{
  "schema": "trureturing-theorist-frontier-v1",
  "exact_statement": {
    "gid": "D5/X_Frontier/<Target>.<declaration>",
    "statement_sha256": "sha256:<64 lowercase hex>"
  },
  "motivation_gids": ["D5/<active-frozen-formal-gid>"],
  "falsifier": "<nonblank falsifier>",
  "search_receipt_gids": ["D5/L/<canonical-library-address>"],
  "computation_receipt_gids": ["D5/E/<canonical-evidence-address>--<kind>"],
  "triage_class": "<theorem|window|wall>"
}
-/
```

To obtain the statement address without guessing, first elaborate and run
`make lean-report`, then run `make theory-candidates` and read the matching
declaration-ready candidate's `content_sha256`; it is the
`CanonicalStatementWriter` address owned by P1. Place that exact address in the
contract, regenerate the report, and confirm replay returns the same address.
Do not derive an address from a file hash, file GID, declaration name, or theory
number.

Run a scoped Lean build while iterating and the canonical producer when final:

```sh
lake build <Dotted.Module.Name>
make lean-report
```

Postcondition: the exact statement elaborates; the module has exactly one open
declaration; the P2 contract binds the replay-stable canonical statement
address; and every GID array is nonempty, sorted, unique, and resolvable by its
owner.

### 6. Run an independent adversarial check

Send the Step 1-5 artifact and receipts to an independent machine seat through
the configured sshx runner. The producing seat must not review itself. Ask the
seat to check:

- equal or stronger duplicates in `D5/`, mathlib, and Library;
- definitional tautology, invented classifiers, vacuous hypotheses, and
  unsatisfiable domains;
- fabricated sources, calculations, GIDs, or statement addresses;
- dropped clauses, weaker hypotheses, changed quantifiers, or hard-coded prose;
- exact P2 shape and the honesty of `theorem|window|wall` triage.

Treat the seat as an untrusted adviser: its only allowed routing result is
`candidate` or `open`, and it never creates truth, approval, proof, or a human
gate. Resolve each concrete finding against source bytes and machine owners,
then rerun the affected prior steps. If the independent seat is unavailable or
a finding cannot be resolved, end evidence-complete `open`.

Postcondition: an independent result and its evidence reference are recorded;
all findings are resolved; and the result is `candidate`.

### 7. Run the complete machine admission chain

Require the intended diff only, then run the canonical full gate:

```sh
git status --short
git rev-parse HEAD
git rev-parse origin/dev
git diff --name-only <resolved-base-sha>...HEAD
make preflight BASE=<resolved-base-sha>
```

`make preflight` owns report production, engineering tests, live P2/SL-002
validation, route/check admission against the protected base, and the three CI
preconditions. Capture the two `git rev-parse` outputs before preflight and
substitute the exact 40-hex base result for `<resolved-base-sha>`; do not let a
moving branch name stand in for that identity. Record the changed-path output
and command exit code in the run-local log. Do not replace preflight with a
hand-picked validator or a producing seat's judgment. If `origin/dev` advances,
follow the live harness diagnostic; never enable strict branch protection or
bypass a failed check. Do not
regenerate an existing generated receipt solely because the selected owner is
its attested input; end `open` and name that coupling instead.

Postcondition: `make preflight BASE=<resolved-base-sha>` exits 0, HEAD still
equals the captured `commit_sha`, and the immutable base SHA, exact changed
paths, and preflight exit code are present in the command log.

### 8. Open the pull request, then observe merge

Commit only the theory-generation artifacts, push the current branch, and use
the repository door:

```sh
git push -u origin <branch>
make pr-open HEAD=<branch> TITLE='<title>' [BODY=<file>]
```

After `make pr-open`, the mutation boundary is closed: do not push further
changes to that branch. Observe the PR through the GitHub REST API until it is
machine-confirmed `MERGED`, then fetch `dev` and verify the returned merge commit
is an ancestor of `origin/dev`. An unmerged `CLOSED` PR, failed required check,
merge conflict, or unavailable observation ends evidence-complete `open` with
the REST payload or diagnostic named.

Apply the bounded observation protocol from `codex-theory-ingest` without
variation. Poll at most 30 times at 60-second intervals, with the first REST and
required-check observations immediate and at most 29 sleeps. Run this long poll
through the host's background-job mechanism and retain its true exit sentinel;
never use shell `&`. Every poll freshly reads the REST PR object and required
checks, validates the fixed JSON fields and captured head SHA, and applies that
protocol's exact exit-code and bucket rules. An ordinary in-progress PR
continues only while budget remains; attempt 30 without a terminal verdict ends
evidence-complete `open` with the latest REST and required-check payloads.

Report `success` only with the REST-confirmed `MERGED` state, `merged_at`, merge
commit SHA, landed `dev` SHA, target declaration GID, selection receipt, six
theorist outputs, adversarial result, and all Step 7 exit codes. There is no
third state.

The resulting declaration remains open. A later `prover` lane may prove it and
must use the repository's current `deliver-check` workflow. This skill never
calls `deposit`, and the target is not a digestion atom for
`codex-formalize`.

## Prohibitions

- Do not edit `Meta/Digestion/**`, `Golden/Frozen/**`, Library or Evidence
  receipts, generated receipts, or any frozen module.
- Do not call `codex-formalize`, `deposit`, `freeze`, or `cover`; do not create
  a substitute for `deliver-check`.
- Do not prove the generated declaration in the same lane, remove its `sorry`,
  call it closed, or claim it is Lean-verified. The only generated truth state
  is machine-derived `open` from `sorryAx`.
- Do not manufacture data, source hits, calculation output, GIDs, statement
  addresses, novelty, worth scores, or successful command results.
- Do not turn natural-language questions into vacuous predicates, definitional
  synonyms, renamed existing theorems, weaker statements, or hard-coded answer
  tables.
- Do not use TASK numbers, theory numbers, filenames, or prose as semantic
  owners. Typed MISSION data and live machine output own routing.
- Do not bypass, weaken, reimplement, or hand-normalize P1 selection, the P2
  validator, Lean report production, sshx independence, or admission.
- Do not add a human approval step. Machine gates decide admissibility; `open`
  honestly records everything they cannot decide.

## What this skill does not own

- Candidate enumeration, ordering, owner override, and lane routing are owned
  by P1 `StrataLint theory-candidates` and `docs/MISSION.md`.
- Frontier contract syntax, address binding, GID resolution, and open-state
  derivation are owned by P2 and its SL-002 validator.
- Worth measurement receipts and complete argmax are not implemented by this
  skill; an open WorthVector remains bootstrap-only.
- Library and Evidence schemas, Lean compilation, report production, admission,
  and PR mechanics remain owned by their existing repository components.
- Creating a missing computation receipt belongs to the `numericist` lane; this
  workflow can only name the handoff and start a new run after that receipt
  lands.
- Proof search, theorem delivery, and freezing belong to the later `prover`
  lane and `deliver-check`.
- External theory-document ingestion belongs to `codex-theory-ingest`;
  residual-atom formalization belongs to `codex-formalize`.

This skill is a packaged state machine over those owners. It is not a parallel
theory system, a truth source, a validator, or a new harness surface.
