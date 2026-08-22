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

Measure, rather than assume, whether the current Lean `make` door and third-party search are usable. Record each probe, its location, its result, and its exit code when it is a command. Run the acceptance matrix below before implementing any local proof.

A missing capability blocks only the transition that uses it. Existing active-frozen facts remain reusable without local Lean. Register a blocked transition with CLAUDE.md item 11's named `wait-for-capability` open; never turn a capability gap into a search-complete claim or a whole-run failure.

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

An exact third-party Lean hit is provenance only in this run-local answer. A17.2 permits repository admission only as `DEPENDENCY` or `PORT`, forbids reproving, and currently has all three admission predicates open; admission belongs to another workflow. Therefore a third-party hit is never this reply's kernel basis.

Do not use SL-028 output to find renamed D5 duplicates. The specification records it as an `Observe` advisory that the admit path does not render, with visibility still open.

Postcondition: each searchable record has the owner-ordered trace for the proposition and its negation shape, or the exact blocked stage is a `wait-for-capability` open; every hit has an address and an explicit reuse disposition.

### 3. Fix the exact statement echo

Only after search has fixed canonical domains, types, declarations, and imports, invoke `agents/echo-template.md`; do not copy its fields here. Complete the clause-coverage account against one exact Lean proposition `P`. An ambiguous or not-formalizable record gets no exact Lean proposition.

Kernel outcomes attach only to exact `P` or its exact negation, never to the original prose or to a nearby statement.

Postcondition: every eligible record has an owner-shaped exact echo whose clause mapping is complete, while ambiguous and not-formalizable records remain explicitly non-kernel branches.

### 4. Adjudicate only a miss

Only after the owner-ordered search completed with no exact hit, and only with measured Lean capability, use a disposable isolated lane to establish `P` or its negation. Select the current build and report doors from `make help`; Lean builds and the canonical report go through those doors. Never use a cold bare `lake build`.

This step is run-local: never deposit, freeze, cover, or edit a receipt. Retain the exact commands, exit codes, diagnostics, pins, and canonical report address. A failed attempt is evidence of failure to prove, never evidence that `P` is false.

Postcondition: owner output contains an exact declaration for `P` or its negation, or the record is `open` with the failed attempts and machine diagnostics; the repository has no new mutation from this skill.

### 5. Derive outcomes from owner facts

Project outcomes mechanically; never author, select, or downgrade an evidence label.

- `proved`: owner facts match exact `P` and carry either an active Frozen event or a successful current `make` door with its exit code, the owner-issued declaration receipt, and the inspector-owned closure contained in the owner-defined standard axiom set.
- `refuted`: the same facts match the exact negation of `P`; keep `P` unchanged.
- `conditional`: an owner-issued exact conditional theorem or certificate matches the clause, while its named empirical premise remains explicit rather than being presented as discharged.
- `open`: no owner-issued fact establishes `P` or its negation, the record is ambiguous, or a required capability transition is open.
- `not-formalized`: the record was classified `not-formalizable` and has no Lean statement.

An active Frozen event remains reusable without current Lean; cite its persisted receipt instead of inventing a current build. `sorryAx`, any non-standard axiom, a failed command, or a statement mismatch can never produce `proved` or `refuted`. Never infer falsity from failure to prove. When owner facts meet a terminal rule, that terminal cannot be downgraded to an informal sink.

Postcondition: every assertion has exactly one mechanically projected outcome, and every formalizable assertion is graded `proved`, `refuted`, `conditional`, or `open`.

### 6. Render the reply

For each assertion render the original clause, the exact proposition or its explicit absence, the outcome, source or report address, exact commands and exit codes, axiom closure, search trace, and persistence marking. Mark evidence `active-frozen` or `run-local`; for run-local evidence include the recorded pins on which it expires.

The outcome vocabulary is closed: `proved`, `refuted`, `conditional`, `open`, `not-formalized`. Do not add an informal assertion grade or any human-review state. Third-party provenance must be visibly distinguished from kernel basis.

Postcondition: the reply is clause-complete, evidence-bearing per assertion, uses only the closed outcome set, and exposes every persistence boundary.

### 7. Close without repository mutation

Compare the repository change set with the pre-run state and leave it unchanged. State explicitly which conclusions are active-frozen and which are run-local. Route any requested durable contribution as a separate task; do not continue into deposit, freeze, coverage, receipts, PR, CI, or merge work.

Postcondition: the answer has been delivered, its persistence scope is explicit, and this invocation has made zero repository changes.

## Acceptance matrix

Before Step 4, run this decision table as the executable echo of the outcome contract and record each case pass or fail. A failed row is a defect to correct before replying, not a human-review state.

| Case | Owner facts | Required result |
| --- | --- | --- |
| Positive `P` | Exact `P`, successful door receipt, standard closure | `proved`; it cannot be downgraded |
| Symmetric negative | Exact negation of `P`, successful door receipt, standard closure | `refuted`; do not alter `P` |
| Sorry despite exit 0 | Exact `P` report contains `sorryAx` | Never `proved` |
| Extra axiom despite exit 0 | Exact `P` closure contains a non-standard axiom | Never `proved` |
| Informal sink | A `formalizable` clause is ungraded or merely called informal | Defect; grade it from owner facts |
| Honest boundary | Ambiguous input; not-formalizable input | `open` with bounded candidates; `not-formalized`; no Lean for either |
| Ordering and capability | Local proof lacks prior D5 or pinned-mathlib trace; a search stage is unavailable | Invalid trace; typed `wait-for-capability` open, never search-complete |
| Frozen reuse without Lean | Exact active Frozen hit; local Lean unavailable | Reuse the frozen terminal with no local Lean |
| Third-party boundary | Exact third-party hit but no admitted in-repo fact | Provenance only and `open`; no reproof or local admission |

This matrix is soft, invoking-agent acceptance evidence. `skills/**` has the same `repository-policy` verification surface as the three existing skills and no per-skill content test. A PR changing this skill must state plainly that it adds no machine test and must not present this matrix as a hard gate.

## Earned hard gates

These are the only hard gates added by this adapter; each names an occurred failure.

- **Reuse exact hits; never reprove them.** CLAUDE.md item 11 records the Knaster-Tarski and golden-ratio reuse precedents, while A17.2 records how the closed third-party path otherwise collapsed into forbidden reproof.
- **Reject a tautological or thin mapping.** `skills/codex-formalize/SKILL.md`, "Mathematical content" and "Deposit substance," records seven definitional-tautology cases and the landed thin-deposit case.
- **Never use a cold bare `lake build`.** CLAUDE.md tool law 3 records issue #2762 and its multi-hour cold-lane failure; PR #2764 is the corresponding repair precedent.
- **Invoke volatile owners; do not copy their contracts.** Spec revision v7.16 R20 at `docs/develop/spec/golden-ledger-repo-spec.md:877` records a stale `skills/` copy after the reference-closure sweep missed that directory.
- **Never claim a command result without its exit code.** `skills/codex-formalize/SKILL.md`, "Process honesty," records the seat that reported a failed Lean build as green.

## Prohibitions

- No deposit, freeze, coverage edit, or receipt edit; the `make` deposit and cover doors and the existing formalize, theorize, and ingest skills own them.
- No second axiom parser, search engine, ledger, or receipt service; `tools/lean-inspector/Inspector.lean` via `make lean-report`, CLAUDE.md item 11, and the frozen ledger own those facts.
- No cold bare `lake build`; the current `make` doors own Lean builds.
- No `requires human review`, `awaiting human`, or equivalent branch; CLAUDE.md item 22 forbids human-review gates.
- No hedging word in place of a measurement; CLAUDE.md section VI owns the typed alternatives.
- No reliance on SL-028 as a consumable duplicate signal; the specification owns its `Observe` effect and records the visibility gap as open.
- No third-party kernel basis, reproof, dependency, or port in this run; A17.2 owns third-party admission.
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
