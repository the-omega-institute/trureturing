---
name: codex-formalize
description: Use when asked to formalize and close an open digestion atom in this repository.
---

# Codex Formalization Workflow

## Install

This is a Codex skill package. Install it by copying the `skills/codex-formalize/` directory into `$CODEX_HOME/skills/` (default `~/.codex/skills`), or load it by naming this `SKILL.md` path directly in a dispatcher. This repository copy is the single source of truth; any installed copy is a projection of it.

## Scope and authority

This file is Codex-specific packaging of repository obligations; it has no authority of its own. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification; `CLAUDE.md` is the invariant frame governing how work is done; and `agents/CONTEXT.md` is the finite-context map and routing aid, not an authority above the specification. Live harness output is the decisive judge of fact about the current tree. If this file disagrees with any of them, they win and this file is the bug.

## Read first

- `CLAUDE.md` - owns the repository's invariant frame and working ethics.
- `agents/CONTEXT.md` - owns the finite-context map, routing, and naming guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md` - owns the normative repository specification.
- The applicable `agents/*.md` role charter - owns role-specific duties.
- `agents/echo-template.md` - owns the statement-echo record.
- `make help` - owns the live catalogue of canonical doors.
- `Meta/StrataLint/` - owns executable admission and repository enforcement.

## State machine

Follow these steps in order. Do not pass a step until its postcondition holds.

### 0. Establish the environment and isolation

Run:

```sh
eval "$(sed -n '/^export PATH=/p' Meta/StrataLint/scripts/local-harness-gate.sh)"
# If not already in a dispatcher-assigned isolated lane:
make worktree NAME=<lane> && cd <created-path-from-output>
pwd -P && git rev-parse --show-toplevel && make dotnet
```

Re-read the current `export PATH` from `Meta/StrataLint/scripts/local-harness-gate.sh` for every task rather than trusting a list quoted elsewhere; its `/usr/sbin` entry must survive because the report supervisor requires `lsof`, which lives there. If a dispatcher already assigned an isolated lane, do not create a second one: confirm the existing lane with the same `pwd -P` / `git rev-parse --show-toplevel` check. Otherwise, the `make worktree` output is JSON whose `path` field names the created path; substitute that value for `<created-path-from-output>` and work only there.

Build through the canonical `make dotnet` door because `make show-atom` runs the Release CLI with `--no-build`.

Before any deposit, require `git status --short` to print nothing except the intended formalization changes. Prefer a fully clean tree before beginning the task. The deposit workflow in `Meta/StrataLint/scripts/workflow/playbook-workflows.sh` stages with `git add -A` in both `commit_phase_a_if_needed` and `commit_all_if_needed`; therefore every change in the tree can enter a deposit commit.

Postcondition: the pinned toolchain is on PATH; `pwd -P` and `git rev-parse --show-toplevel` agree with the assigned or created isolated lane; `make dotnet` has built the CLI so `make show-atom` succeeds; and no unrelated or unexplained change is present.

### 1. Choose exactly one open atom

Inspect candidate snapshots in `Generated/echo-residuals/<source_id>.md`. Treat them only as candidate listings. Obtain the authoritative atom text with:

```sh
make show-atom ATOM_ID=<id>
```

Never quote the projection as authoritative. Prefer an atom with few unresolved subitems and an elementary, self-contained statement.

Postcondition: one atom ID is selected and its verified `make show-atom` output is retained as the statement source.

### 2. Echo the statement before proving it

Follow `agents/echo-template.md`. Write a clause-level mapping from every quantifier, domain, hypothesis, conclusion, and generality claim in the authoritative atom text to the intended Lean declaration. Account for every unresolved subitem.

If an ambiguity cannot be resolved without weakening the claim, stop and report the result as `open`.

Postcondition: every source clause has one intended Lean counterpart, or the task has ended as `open` with the ambiguity named.

### 3. Search the library before proving

Apply `CLAUDE.md` 11, "library before proof." Search pinned mathlib and the repository's `D5/` declarations for the complete statement and for lemmas that close its dependencies. Record every query verbatim and record whether it hit.

If the result exists upstream, import and apply it. Do not reprove it: a reproof of an existing declaration creates a second source of truth.

Postcondition: the search trace is recorded and every hit is either reused or accompanied by a concrete explanation of why it is not the same claim.

If the search cannot be completed faithfully, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 4. Learn the current artifact shape

Run:

```sh
git log --no-merges -20 --format=%H --grep='^formalize: deposit'
git show <sha>
```

Read the most recent actual `formalize: deposit` commit. That commit is the live template for the exact Lean header shape, the `.scribe.cs` mirror shape, and the files touched by deposit. Copy its shape rather than formats remembered or restated here. If this file and that commit disagree, the commit wins.

Postcondition: the chosen template SHA and its touched paths are recorded, and the planned artifacts follow that observed shape.

### 5. Write and compile the artifacts

Write the Lean module and its `.scribe.cs` mirror using the live template. Discover the current path-to-GID rule from that template and the live path-policy owner; do not rely on a remembered grammar.

A new theorem must go in a new Lean module. Before writing into an existing module, check whether it has an active Freeze event:

```sh
module_path='D5/path/Module.lean'; grep -l -F "$module_path" Meta/StrataLint/Golden/Frozen/accepted/*.json
```

Exit 0 with an accepted-record path means frozen; exit 1 with no output means not frozen (any other result is a failed check). The frozen ledger pins the module's declaration set, not just its bytes, so it refuses adding a declaration to a frozen module. Reattest covers changed bytes with an unchanged declaration set; it is not an escape hatch for adding a declaration. If the atom genuinely belongs inside an existing frozen module, do not edit it: end `open`, naming that module and the frozen-ledger constraint.

Before creating the new module, set `lean_dir` to its target directory and `blueprint_dir` to the corresponding `Blueprint/` mirror directory, then measure both and confirm that adding one counted file to each stays within the limit:

```sh
lean_count=$(git ls-files "$lean_dir" | awk 'END { print NR+0 }'); blueprint_count=$(git ls-files "$blueprint_dir" | awk '!/\.md$/ { n++ } END { print n+0 }'); printf '%s %s\n%s %s\n' "$lean_dir" "$lean_count" "$blueprint_dir" "$blueprint_count"; test $((lean_count + 1)) -le 12 && test $((blueprint_count + 1)) -le 12
```

Blueprint `.md` projections are excluded from capacity, but `.scribe.cs` sources count. If the natural target directory is full, do not place the module in a semantically wrong directory to evade the limit: split the bucket, register the new domain in `Meta/domains.yaml`, place the module in the new directory, and carry the protected-surface cost for the conservative-extension gate to judge. A protected-surface change is priced work, not a stopping condition. Reserve `open` for what is genuinely unresolvable, such as an ambiguity that cannot be settled without weakening the claim or a proof that will not close, never for work that merely costs more.

Run:

```sh
make lean
```

Judge completion only by exit code, never elapsed time or quiet output.

Postcondition: both source artifacts exist in the observed shape and `make lean` exits 0.

If a faithful proof cannot be made to compile, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 6. Run the fidelity and non-hollowness gate

Complete every evidence item in the checklist below. A green compiler and harness do not discharge this step.

Postcondition: every checklist item has evidence and none is `ASSUMED-UNVERIFIED`; otherwise deposit is blocked.

If any checklist item cannot be evidenced, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 7. Land PR-1: deposit the proof and receipt

Only after Step 6 passes, run:

```sh
make deposit ATOM_ID=<id> GID=<D5/Path/Module.theorem_name>
make preflight
```

Both commands must exit 0. Judge them only by exit code.

If `make deposit` or `make preflight` exits nonzero, stop and end as `open`. Report the failed command and exit code, machine diagnostics, touched paths, and the actual resulting tree and commit state; `deposit` may already have produced commits before failing.

Push the deposit branch and open PR-1 through the repository door:

```sh
git push -u origin <deposit-branch>
make pr-open HEAD=<deposit-branch> TITLE='<deposit-title>' [BODY=<file>]
```

Wait until PR-1 is merged and its commit is contained in `origin/dev`. Do not run `make cover` on the deposit branch: the formalization receipt has authority only after it is part of the protected baseline.

Postcondition: PR-1 is merged, and the proof plus `Meta/Digestion/formalizations/<atom_id>.v1.json` are contained in `origin/dev` while the atom remains uncovered.

### 8. Land PR-2: cover from a fresh post-merge lane

Create a fresh independent lane from the landed `origin/dev`, then run:

```sh
make worktree NAME=<cover-lane> BASE=origin/dev
cd <created-path-from-output>
make cover ATOM_ID=<id> GID=<gid>
make preflight
git push -u origin <cover-branch>
make pr-open HEAD=<cover-branch> TITLE='<cover-title>' [BODY=<file>]
```

The receipt must already belong to the protected fork point when PR-2 is admitted. The cover command may begin while a clean fresh lane still has `HEAD` equal to its landed base; it creates the cover commit itself. A receipt introduced only in PR-2 has no authority even if a candidate-local revision is passed as the command's base, because final admission validates against the protected fork point independently of the CLI argument. The door arms auto-merge; after opening either pull request, do not push further changes to that branch.

If the dispatched sandbox forbids git writes, state that constraint explicitly and hand the exact two-PR commands above, with substituted arguments, to the caller; do not report `success` as though the work landed. Otherwise report `success` only after both pull requests are opened, with touched paths, door-produced commit subjects, every relevant exit code, and completed fidelity-gate evidence. Or report `open`, naming the stopping step and carrying every evidence class reached; mark each unreached class not run and explain why. There is no third outcome.

Postcondition: PR-2 is opened from a fresh post-PR-1 baseline, or the task ends with evidence-complete `open`.

## Fidelity and non-hollowness gate

Before Step 7, the producing seat must answer every item with concrete evidence. This checklist collects producer-side evidence; it is not machine-verified and does not itself prove non-hollowness. The repository's own machine gate is deferred by the skipped `CoverAtomEnvelopeTests.cs` signature-match test cited below. An independent adversarial reviewer, not the producing seat, would turn this evidence into verification.

- Conclusion substance: show that the conclusion is not `True`, not definitionally equal to `True`, and not a restatement of a hypothesis.
- Hypothesis satisfiability: exhibit a Lean term witnessing the hypotheses that elaborates in the pinned toolchain, such as a checked `example` in the module or a term the seat states and checks, and carry that term in the report. Prose asserting or naming a witness does not discharge this item; if no compiling witness can be produced, the outcome is `open` and deposit is blocked.
- Domain inhabitance: exhibit a Lean term inhabiting the domain that elaborates in the pinned toolchain, such as a checked `example` in the module or a term the seat states and checks, and carry that term in the report. Prose asserting or naming an inhabitant does not discharge this item.
- Proof substance: show that the statement carries content beyond unfolding a definition the producing seat itself introduced, whatever tactic closes it.
- Duplicate search: cite the Step 3 trace showing this is not a renamed duplicate of a mathlib or `D5/` declaration.
- Clause fidelity: place the authoritative atom clauses beside the Lean clauses one-to-one, mapping every clause to an exact Lean binder, hypothesis, or conclusion. The dropped-or-weakened set must be empty; any weakening, omission, or unresolved ambiguity forces `open` before deposit.
- Rendered-statement fidelity: read the emitted Blueprint `.md` for this document and compare its displayed statement against the Lean declaration symbol by symbol; use a neighbouring landed mirror as a shape check.
  The formula DSL and writer own tokens that can be valid LaTeX and structurally accepted yet mean something different from the theorem, so `emit` exiting 0 is not evidence that the rendering is faithful.
  A mismatch blocks deposit; resolve it against `Meta/StrataLint/StrataLint.Scribe/Ast/FormulaDsl.cs` and `Meta/StrataLint/StrataLint.Scribe/Writers/LatexWriter.cs`, or end the task `open`.

Any item without evidence blocks deposit. Mark an unverified fact exactly `ASSUMED-UNVERIFIED`; never replace measurement with hedging language. The repository's current signature-match test explicitly leaves this gap open: `CoverAtomEnvelopeTests.cs` says an unchanged pre-committed `theorem t : True` would pass, so compilation, deposit, and cover do not certify fidelity.

## Prohibitions

- No `sorry` outside `D5/X_Frontier/`; the Lean admission harness owns this rule.
- No new axiom; the Lean admission harness and axiom policy own this rule.
- Never hand-write a status field; `agents/CONTEXT.md` and status derivation own it.
- Never hand-edit generated projections; their canonical producers own them.
- Never hand-edit the frozen ledger; the deposit door owns it.
- Never add a declaration to a module with an active Freeze event; the frozen ledger owns this constraint.
- Never exceed directory capacity; `Meta/StrataLint/StrataLint.Engine/Rules/RepositoryRules.Structure.cs` owns this rule.
- Never hand-edit formalization receipts; the deposit and cover doors own them.
- Never weaken the echoed statement to make a proof close; the statement echo and this fidelity gate own that obligation.
- Never invent a "needs human review" outcome; `CLAUDE.md` 22 forbids human-review gates outright.

## What this skill does not own

- Path policy is owned by `Meta/StrataLint/StrataLint.Engine/Coordinates/RepositoryPathPolicy.cs` and its registered policy data.
- Capacity limits are owned by `Meta/StrataLint/StrataLint.Engine/Rules/RepositoryRules.Structure.cs`.
- Lean header shape is owned by the live harness and demonstrated by the latest landed deposit.
- Import direction is owned by the repository specification and its StrataLint rules.
- Admission, freezing, receipts, coverage, and status are owned by the canonical `make` doors and `Meta/StrataLint/`.

This skill names each concern's owner without reproducing its definitions or thresholds. The prohibitions above are pointers that carry the owner's name. Discover each concern's current form from its owner; the harness is the judge.
