---
name: codex-formal-answer
description: Use when answering natural-language mathematical assertions with clause-complete formalization and owner-issued Lean evidence, without depositing repository truth.
---

# Codex Formal Answer Workflow

## Install

This is a Codex skill package. Install it by copying the `skills/codex-formal-answer/` directory into `$CODEX_HOME/skills/` (default `~/.codex/skills`), or load it by naming this `SKILL.md` path directly in a dispatcher. This repository copy is the single source of truth; any installed copy is a projection of it.

## Scope and authority

This skill is a thin adapter for one invocation, from a user's natural-language input to an evidence-bearing reply. It owns only (1) the clause-complete mapping from that input to exact propositions and (2) the per-assertion rendering of facts issued by existing owners. It owns no proof status and defaults to zero repository mutation.

A reply is a proof-carrying projection over existing truth, not a new truth plane or an automatic frozen node. A request for a durable contribution is a separate task routed to the existing Frontier, formalization, or admission workflow; answering never deposits or freezes by itself.

This file is Codex-specific packaging of repository obligations; it has no authority of its own. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification, `CLAUDE.md` is the invariant frame, and live owner output decides facts about the current tree. If this file disagrees with an owner, the owner wins and this file is the bug.

## Read first

- `CLAUDE.md`, especially item 11, item 22, and section VI.
- `agents/CONTEXT.md` for the finite-context map and routing guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md`, especially 1.4 and A17.2.
- `agents/echo-template.md`, which owns the exact-statement record.
- `make help`, which owns the live catalogue of canonical doors.
- `tools/lean-inspector/Inspector.lean` and the canonical `make lean-report` output, which own declaration axiom closures.
- The existing `codex-formalize`, `codex-theorize`, or `codex-theory-ingest` skill only when a separate durable task is routed to it.

## State machine

Follow these steps in order. Do not pass a step until its postcondition holds.

### 0. Measure capabilities

Measure, rather than assume, whether the current Lean `make` door and third-party search are usable. Record each probe, its location, its result, and its exit code when it is a command. After owner facts exist, use the runtime decision table below at Step 5.

Under the current text of `CLAUDE.md` item 11, a missing capability blocks only the transition that uses it, active-frozen facts remain reusable without local Lean, and a blocked transition takes the named `wait-for-capability` open rather than becoming a search-complete claim or whole-run failure.

Postcondition: every relevant capability has measured evidence, and each unavailable transition has the owner-defined typed open while independent assertions continue.

### 1. Inventory raw clauses

Split the input into assertion records while preserving each clause verbatim. For each record, account for every material phrase in a pending semantic mapping and classify it as exactly one of:

- `formalizable`: it can be stated exactly as a proposition; this says nothing about decidability or provability.
- `conditional-empirical`: its force depends on an explicit empirical condition that must remain visible.
- `ambiguous`: retain a bounded set of materially distinct candidate formalizations and keep the assertion open. Never claim the set is exhaustive without a finiteness proof, and never ask the user to choose.
- `not-formalizable`: return `not-formalized` and create no ornamental Lean.

Separate explanatory prose from assertions. Explanations need no grade; every assertion does.

Postcondition: every assertion and every material clause is present exactly once, with original wording, classification, and clause coverage; no assertion has been dropped or weakened.

### 2. Coordinate and search for reuse

Execute CLAUDE.md item 11's current owner-defined ordered search before fixing the typed echo. At every stage search both the pending proposition and the shape of its negation or counterexample. Record the verbatim query, where it ran, hit or miss, and the address of every hit. A textual hit discharges nothing until it is exactly reused or applied.

On the current text of specification A17.2 (`docs/develop/spec/golden-ledger-repo-spec.md:163`), exact third-party Lean reuse has only dependency or port admission, reproof is forbidden, and all three admission predicates remain `open`. This invocation performs no admission, so an exact third-party hit is provenance only and never this reply's kernel basis.

On the current text of specification 11.20.4 (`docs/develop/spec/golden-ledger-repo-spec.md:523` and `:533`), do not use SL-028 output to find renamed D5 duplicates: it is an `Observe` advisory that the admit path does not render, with visibility still `open`.

Postcondition: each searchable record has the owner-ordered trace for the proposition and its negation shape, or the exact blocked stage is a `wait-for-capability` open; every hit has an address and an explicit reuse disposition.

### 3. Fix the exact statement echo

Only after search has fixed canonical domains, types, declarations, and imports, invoke `agents/echo-template.md`; do not copy its fields here. Complete the clause-coverage account against one exact Lean proposition `P`. An ambiguous or not-formalizable record gets no exact Lean proposition.

Kernel outcomes attach only to exact `P` or its exact negation, never to the original prose or to a nearby statement.

Postcondition: every eligible record has an owner-shaped exact echo whose clause mapping is complete, while ambiguous and not-formalizable records remain explicitly non-kernel branches.

### 4. Construct a report-owned run-local declaration

After the owner-ordered search, and only with measured Lean capability, follow the current reuse-before-proof rule in `CLAUDE.md` item 11 in a disposable isolated lane on exactly two occasions: (1) for an exact in-repository or pinned-mathlib hit, create the thinnest honest wrapper that imports and applies the hit to declare exact `P` or its negation; this is reuse, not reproof, and a wrapper that restates or reproves the hit instead of applying it is forbidden; (2) for a genuine miss, create a local proof declaration for exact `P` or its negation. Both forms give the canonical report a run-local managed declaration it can own and issue a declaration receipt for. Select the current build and report doors from the current `make help`; never use a cold bare `lake build`.

This step is run-local: never deposit, freeze, cover, or edit a receipt. Retain the exact commands, exit codes, diagnostics, pins, and canonical report address. A failed attempt is evidence of failure to prove, never evidence that `P` is false.

Postcondition: owner output contains an exact declaration for `P` or its negation, or the record is `open` with the failed attempts and machine diagnostics; the repository has no new mutation from this skill.

### 5. Derive outcomes from owner facts

Project outcomes mechanically; never author, select, or downgrade a label. Before applying the ordered rules, discard any purported kernel evidence unless it matches the exact statement and carries either an active Frozen receipt or a successful current `make` door receipt with its exit code, plus the owner-issued declaration receipt and inspector-owned closure contained in the owner-defined standard axiom set. For current evidence, the door receipt, declaration receipt, closure, and report/input attestation must form one bundle from a single production for the current repository inputs: `tools/scripts/lean-report-pair.sh` emits the `input_address` and `report_sha256` join keys, and `tools/scripts/report/lean-report-input.sh verify` verifies the report and current repository input. Never assemble evidence across runs or pins. `sorryAx`, any non-standard axiom, a failed command, or a statement mismatch makes that evidence ineligible. Apply the first matching rule:

1. `not-formalized` when the record is `not-formalizable` and has no Lean statement.
2. `conditional` when the record is `conditional-empirical`, exact `P` is conditional with its named empirical premise undischarged, and eligible owner evidence establishes exact `P`.
3. `proved` when eligible owner evidence establishes exact `P` for any other record.
4. `refuted` when eligible owner evidence establishes the exact negation of `P`; keep `P` unchanged.
5. `open` otherwise, including an ambiguous record, an unavailable required capability, or no eligible evidence for `P` or its negation.

`conditional` is for kernel-established conditional-empirical `P`, while `proved` is for kernel-established exact `P` outside that branch. Thus, when exact `P` is itself conditional and the kernel establishes it, the single outcome is `conditional`, not `proved`, and the reply must render the undischarged empirical premise. An active Frozen receipt remains reusable without current Lean. Never infer falsity from failure to prove or downgrade a terminal to an informal sink.

Postcondition: every assertion has exactly one mechanically projected outcome, and every formalizable assertion is graded `proved`, `refuted`, `conditional`, or `open`.

### 6. Render the reply

For each assertion render the original clause, the exact proposition or its explicit absence, the outcome, source or report address, exact commands and exit codes, axiom closure, search trace, and persistence marking. Mark evidence `active-frozen` or `run-local`; for run-local evidence include the recorded pins on which it expires.

The outcome vocabulary is closed: `proved`, `refuted`, `conditional`, `open`, `not-formalized`. Do not add an informal assertion grade or any human-review state. Third-party provenance must be visibly distinguished from kernel basis.

Postcondition: the reply is clause-complete, evidence-bearing per assertion, uses only the closed outcome set, and exposes every persistence boundary.

### 7. Close without repository mutation

Compare the repository change set with the pre-run state and leave it unchanged. State explicitly which conclusions are active-frozen and which are run-local. Route any requested durable contribution as a separate task; do not continue into deposit, freeze, coverage, receipts, PR, CI, or merge work.

Postcondition: the answer has been delivered, its persistence scope is explicit, and this invocation has made zero repository changes.

## Decision table and acceptance obligation

At runtime, after owner facts exist, Step 5 projects each assertion through exactly one row of this decision table. Its record carries the specific address of each owner fact that assertion actually has for that row; it never fabricates addresses for other rows.

At skill-change time, before changing this file, the editor must verify that the table is exhaustive and mutually exclusive against Step 5's ordered rules, and a pull request changing this file carries that verification as the executable echo required by `CLAUDE.md` item 11. A failed verification is a defect, not a human-review state. Under the current `skills/**` classification at `Meta/FILEMAP.toml:414-420`, this is **SOFT** acceptance evidence on the existing `repository-policy` surface, not a hard gate or a per-skill machine test.

| Case | Owner facts | Required result |
| --- | --- | --- |
| Not-formalized boundary | `not-formalizable`; no Lean statement | `not-formalized` |
| Conditional empirical | `conditional-empirical`; exact conditional `P` with named premise undischarged; eligible evidence for `P` | `conditional` |
| Positive `P`, including Frozen reuse; no informal sink | `formalizable`; exact `P`; eligible evidence for `P`, whether current or active-frozen | `proved` |
| Symmetric negative | `formalizable` or `conditional-empirical`; exact `P`; no eligible evidence for `P`; eligible evidence for its exact negation | `refuted` |
| Open boundary | Every remaining record, including addressed ambiguity; missing required search or capability; no eligible evidence because the only candidate has `sorryAx`, a non-standard axiom, a failed door, or a statement mismatch; or exact third-party provenance under the current A17.2 with no active Frozen or current owner declaration receipt for `P` or its exact negation | `open` |

## Earned hard gates

These are the only hard gates added by this adapter; each names an occurred failure.

- **Reuse exact hits; never reprove them.** This is the current reading of `CLAUDE.md` item 11's Knaster-Tarski and golden-ratio precedents and specification A17.2 (`docs/develop/spec/golden-ledger-repo-spec.md:163`), whose incident is the third-party path collapsing into forbidden reproof.
- **Reject a tautological or thin mapping.** This is the current reading of `skills/codex-formalize/SKILL.md`, "Mathematical content" and "Deposit substance," which record seven definitional-tautology cases and the landed thin-deposit case.
- **Never use a cold bare `lake build`.** This is the current reading of `CLAUDE.md` tool law 3, which records issue #2762's multi-hour cold-lane failure and PR #2764's repair.
- **Invoke volatile owners; do not copy their contracts.** This is the current reading of specification revision v7.16 R20 at `docs/develop/spec/golden-ledger-repo-spec.md:877`, which records a stale `skills/` copy after a reference-closure sweep missed that directory.
- **Never claim a command result without its exit code.** This is the current reading of `skills/codex-formalize/SKILL.md`, "Process honesty," which records the seat that reported a failed Lean build as green.

## Prohibitions

- No deposit, freeze, coverage edit, or receipt edit; the `make` deposit and cover doors and the existing formalize, theorize, and ingest skills own them.
- No second axiom parser, search engine, ledger, or receipt service; `tools/lean-inspector/Inspector.lean` via `make lean-report`, CLAUDE.md item 11, and the frozen ledger own those facts.
- Under the current `CLAUDE.md` tool law 3 and `make help`, no cold bare `lake build`; the current `make` doors own Lean builds.
- Under the current `CLAUDE.md` item 22, no `requires human review`, `awaiting human`, or equivalent branch.
- Under the current `CLAUDE.md` section VI, no hedging word in place of a measurement; use its typed alternatives.
- Under the current specification 11.20.4 (`docs/develop/spec/golden-ledger-repo-spec.md:523` and `:533`), no reliance on SL-028 as a consumable duplicate signal while its `Observe` output remains unrendered.
- Under the current specification A17.2 (`docs/develop/spec/golden-ledger-repo-spec.md:163`), no third-party kernel basis, reproof, dependency, or port in this run; its admission belongs to another workflow.
- No automatic conversion of a reply into a repository node; the F-plane admission and freezing workflows own durable truth.

## What this skill does not own

- Search order and `wait-for-capability`: CLAUDE.md item 11.
- Third-party admission: specification A17.2.
- Truth-state syntax: specification 1.4.
- Axiom authority: `tools/lean-inspector/Inspector.lean`, the canonical `make lean-report`, and the owner-pinned standard axiom set.
- Lean build doors: the root `Makefile` as listed by `make help`.
- Freezing, receipts, and coverage: the deposit and cover doors and their existing skills.
- PR mechanics: `make pr-open`.

This skill names each owner without reproducing its thresholds, grammars, or protocols. The owners and their live machine output always win.
