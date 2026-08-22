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

This file is Codex-specific packaging of repository obligations; it has no authority over owner facts. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification, `CLAUDE.md` is the invariant frame, and live owner output decides facts about the current tree. Any current-state summary below is a non-load-bearing reading: it creates no rule independent of its owner, and if the owner disagrees, follow the owner and treat the summary here as void.

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

Measure, rather than assume, whether the current Lean `make` door and third-party search are usable. Record each probe, its location, its result, and its exit code when it is a command. After owner facts exist, apply Step 5's ordered rules.

Use the capability owner's typed result for each transition. A capability failure is never negative evidence about `P`.

Postcondition: every relevant capability has measured evidence, and each unavailable transition has an addressed owner-issued capability fact while independent assertions continue.

### 1. Inventory raw clauses

Split the input into assertion records while preserving each clause verbatim. For each record, account for every material phrase in a pending semantic mapping and classify it as exactly one of:

- `formalizable`: it can be stated exactly as a proposition; this says nothing about decidability or provability.
- `conditional-empirical`: its force depends on an explicit empirical condition that must remain visible.
- `ambiguous`: retain a bounded set of materially distinct candidate formalizations without choosing one. Never claim the set is exhaustive without a finiteness proof, and never ask the user to choose.
- `not-formalizable`: no exact proposition can be stated; create no ornamental Lean.

Separate explanatory prose from assertions. Explanations need no grade; every assertion does.

Postcondition: every assertion and every material clause is present exactly once, with original wording, classification, and clause coverage; no assertion has been dropped or weakened.

### 2. Coordinate and search for reuse

Execute CLAUDE.md item 11's current owner-defined ordered search before fixing the typed echo. At every stage search both the pending proposition and the shape of its negation or counterexample. Record the verbatim query, where it ran, hit or miss, and the address of every hit. A textual hit discharges nothing until it is exactly reused or applied.

Third-party reuse and admission are owned by specification A17.2. This invocation performs no admission: record an exact third-party hit as provenance, and let Step 5 accept it as kernel basis only if an owner separately issues eligible in-repository evidence.

Invoke specification 11.20.4 for the current SL-028 semantics. This file neither defines its admission effect nor assumes its output is visible; record only output actually received.

Postcondition: each searchable record has the owner-ordered trace for the proposition and its negation shape, or the exact blocked stage has an addressed owner-issued `wait-for-capability` fact; every hit has an address and an explicit reuse disposition.

### 3. Fix the exact statement echo

Only after search has fixed canonical domains, types, declarations, and imports, invoke `agents/echo-template.md`; do not copy its fields here. Complete the clause-coverage account against one exact Lean proposition `P`. An ambiguous or not-formalizable record gets no exact Lean proposition.

Kernel outcomes attach only to exact `P` or its exact negation, never to the original prose or to a nearby statement.

Postcondition: every eligible record has an owner-shaped exact echo whose clause mapping is complete, while ambiguous and not-formalizable records remain explicitly non-kernel branches.

### 4. Construct a report-owned run-local declaration

After the owner-ordered search, and only with measured Lean capability, follow the current reuse-before-proof rule in `CLAUDE.md` item 11 in a disposable isolated lane on exactly two occasions: (1) for an exact in-repository or pinned-mathlib hit, create the thinnest honest wrapper that imports and applies the hit to declare exact `P` or its negation; this is reuse, not reproof, and a wrapper that restates or reproves the hit instead of applying it is forbidden; (2) for a genuine miss, create a local proof declaration for exact `P` or its negation. Both forms give the canonical report a run-local managed declaration it can own and issue a declaration receipt for. Select the current build and report doors from the current `make help`; never use a cold bare `lake build`.

This step is run-local: never deposit, freeze, cover, or edit a receipt. Retain the exact commands, exit codes, diagnostics, pins, and canonical report address. A failed attempt is evidence of failure to prove, never evidence that `P` is false.

Postcondition: owner output contains an exact declaration for `P` or its negation, or retains the failed attempts and machine diagnostics as facts for Step 5; the repository has no new mutation from this skill.

### 5. Derive outcomes from owner facts

Project outcomes mechanically; never author, select, or downgrade a label. Before applying the ordered rules, discard any purported kernel evidence unless it matches the exact statement and carries either an active Frozen receipt or a successful current `make` door receipt with its exit code, plus the owner-issued declaration receipt and inspector-owned closure contained in the owner-defined standard axiom set. For current evidence, the door receipt, declaration receipt, closure, and report/input attestation must form one bundle from a single production for the current repository inputs: `tools/scripts/lean-report-pair.sh` emits the `input_address` and `report_sha256` join keys, and `tools/scripts/report/lean-report-input.sh verify` verifies the report and current repository input. Never assemble evidence across runs or pins. `sorryAx`, any non-standard axiom, a failed command, or a statement mismatch makes that evidence ineligible. Apply the first matching rule:

1. `not-formalized` when the record is `not-formalizable` and has no Lean statement.
2. `conditional` when the record is `conditional-empirical`, exact `P` is conditional with its named empirical premise undischarged, and eligible owner evidence establishes exact `P`.
3. `proved` when eligible owner evidence establishes exact `P` for any record not matched above.
4. `refuted` when eligible owner evidence establishes the exact negation of `P` for any record not matched above; keep `P` unchanged.
5. `open` otherwise, including an ambiguous record, an unavailable required capability, a provenance-only third-party hit, or no eligible evidence for `P` or its negation.

These rules are a total function over reachable owner-fact states: rule 1 handles the reachable not-formalizable/no-statement state; rules 2-4 handle eligible positive or negative evidence in order; and rule 5 catches every remainder, including ambiguity, unavailable capability, and ineligible evidence. First-match evaluation stops at one rule, so the projected domains are mutually exclusive by construction and exactly one outcome results. In particular, a `conditional-empirical` record whose named empirical premise is discharged cannot match rule 2; eligible evidence for exact `P` matches rule 3 exactly once, yielding `proved`.

`conditional` applies only while the named empirical premise is undischarged. An active Frozen receipt remains reusable without current Lean. Never infer falsity from failure to prove or downgrade a terminal to an informal sink.

Postcondition: every assertion has exactly one mechanically projected outcome, and every formalizable assertion is graded `proved`, `refuted`, `conditional`, or `open`.

### 6. Render the reply

For each assertion render the original clause, the exact proposition or its explicit absence, the outcome, source or report address, exact commands and exit codes, axiom closure, search trace, and persistence marking. Mark evidence `active-frozen` or `run-local`; for run-local evidence include the recorded pins on which it expires.

The outcome vocabulary is closed: `proved`, `refuted`, `conditional`, `open`, `not-formalized`. Do not add an informal assertion grade or any human-review state. Third-party provenance must be visibly distinguished from kernel basis.

Postcondition: the reply is clause-complete, evidence-bearing per assertion, uses only the closed outcome set, and exposes every persistence boundary.

### 7. Close without repository mutation

Compare the repository change set with the pre-run state and leave it unchanged. State explicitly which conclusions are active-frozen and which are run-local. Route any requested durable contribution as a separate task; do not continue into deposit, freeze, coverage, receipts, PR, CI, or merge work.

Postcondition: the answer has been delivered, its persistence scope is explicit, and this invocation has made zero repository changes.

## Acceptance obligation

At runtime, Step 5's ordered rules are the sole outcome authority. Each assertion record carries the specific address of every owner fact it actually relied on; it never fabricates unused owner addresses.

At skill-change time, before changing this file, the editor must verify that the ordered rules remain a total function: exhaustive over reachable owner-fact states and single-valued by first-match evaluation. A pull request changing this file carries that verification as the executable echo required by `CLAUDE.md` item 11. Failed verification is a defect, not a human-review state. This is a **SOFT** acceptance obligation and adds no per-skill machine test; the FILEMAP owner remains authoritative for repository-policy classification.

## Earned hard gates

These are the only hard gates added by this adapter; each names an occurred failure.

- **Honor the owner-issued reuse disposition; never invent a reproof path.** Invoke `CLAUDE.md` item 11 and specification A17.2 (`docs/develop/spec/golden-ledger-repo-spec.md:163`). The occurred incident is the third-party path collapsing into forbidden reproof.
- **Reject a tautological or thin mapping.** Invoke `skills/codex-formalize/SKILL.md`, "Mathematical content" and "Deposit substance," which record seven definitional-tautology cases and the landed thin-deposit case.
- **Never use a cold bare `lake build`.** Invoke `CLAUDE.md` tool law 3, which records issue #2762's multi-hour cold-lane failure and PR #2764's repair.
- **Treat owner summaries here as non-load-bearing.** Invoke the owner before use; any summary is void on disagreement and may not create an independent rule. Specification revision v7.16 R20 at `docs/develop/spec/golden-ledger-repo-spec.md:877` records the stale `skills/` copy left when a reference-closure sweep missed that directory.
- **Never claim a command result without its exit code.** Invoke `skills/codex-formalize/SKILL.md`, "Process honesty," which records the seat that reported a failed Lean build as green.

## Prohibitions

- No deposit, freeze, coverage edit, or receipt edit; the `make` deposit and cover doors and the existing formalize, theorize, and ingest skills own them.
- No second axiom parser, search engine, ledger, or receipt service; `tools/lean-inspector/Inspector.lean` via `make lean-report`, CLAUDE.md item 11, and the frozen ledger own those facts.
- No `requires human review`, `awaiting human`, or equivalent branch; `CLAUDE.md` item 22 owns that prohibition.
- No hedging word in place of a measurement; `CLAUDE.md` section VI owns its typed alternatives.
- No third-party admission in this run; specification A17.2 owns that separate workflow.
- No automatic conversion of a reply into a repository node; the F-plane admission and freezing workflows own durable truth.

## What this skill does not own

- Search order and `wait-for-capability`: CLAUDE.md item 11.
- Third-party admission: specification A17.2.
- Truth-state syntax: specification 1.4.
- Axiom authority: `tools/lean-inspector/Inspector.lean`, the canonical `make lean-report`, and the owner-pinned standard axiom set.
- Lean build doors: the root `Makefile` as listed by `make help`.
- Freezing, receipts, and coverage: the deposit and cover doors and their existing skills.
- PR mechanics: `make pr-open`.

This skill names each owner and states only the minimum non-load-bearing reading needed to run the workflow. Owners and their live machine output always win; a conflicting local sentence is void.
