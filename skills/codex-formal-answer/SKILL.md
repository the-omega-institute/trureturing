---
name: codex-formal-answer
description: Use when answering natural-language mathematical, conceptual, philosophical, or metaphysical assertions and questions by discovering repository theory, proving a reusable general theorem, specializing it to the concrete proposition, and routing substantive new Lean results into the repository's durable formalization workflow.
---

# Codex Formal Answer Workflow

## Install

This is a Codex skill package. Install it by copying the `skills/codex-formal-answer/` directory into `$CODEX_HOME/skills/` (default `~/.codex/skills`), or load it by naming this `SKILL.md` path directly in a dispatcher. This repository copy is the single source of truth; any installed copy is a projection of it.

## Scope and authority

This skill coordinates one invocation from a user's natural-language input to an evidence-bearing reply and, when the work produces a substantive new reusable Lean result, to its durable repository owner. It owns (1) the clause-complete mapping from that input to exact propositions, (2) the `P`/`G`/`S` bridge, and (3) the durability disposition. It owns no proof status, admission decision, frozen receipt, or pull-request mechanism.

A reply remains a proof-carrying projection over owner-issued truth, not a new truth plane. The workflow must not strand a substantive new reusable theorem in a disposable file merely because the immediate reply can cite run-local evidence. It routes such a theorem through the existing Frontier, formalization, and admission owners; exact reuse, thin wrappers, and scenario-only specializations create no duplicate repository node.

This file is Codex-specific packaging of repository obligations; it has no authority over owner facts. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification, `CLAUDE.md` is the invariant frame, and live owner output decides facts about the current tree. Any current-state summary below is a non-load-bearing reading: it creates no rule independent of its owner, and if the owner disagrees, follow the owner and treat the summary here as void.

## Read first

- `CLAUDE.md`, especially item 11, item 22, and section VI.
- `agents/CONTEXT.md` for the finite-context map and routing guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md`, especially 1.4 and A17.2.
- `agents/echo-template.md`, which owns the exact-statement record.
- `make help`, which owns the live catalogue of canonical doors.
- `tools/lean-inspector/Inspector.lean` and the canonical `make lean-report` output, which own declaration axiom closures.
- `skills/codex-formalize/SKILL.md` in full as soon as `deposit-new` becomes a candidate; it owns the durable theorem workflow and its substance gate.
- `skills/codex-theorize/SKILL.md` or `skills/codex-theory-ingest/SKILL.md` only when the live owner routes a valuable statement through Frontier or source ingestion before formalization.

## Repository concept search

This repository is not merely a library of conventional mathematical theorems. It contains typed and narrative theories of concepts, interpretation, identity, ontology, metaphysics, language, ethics, agency, religion, and other domains. An absent mathlib theorem or an absent exact keyword is therefore not evidence that an input is unformalizable. Before fixing `P`, execute this repository-first discovery path and retain every query, result count, address, cross-reference, and reuse disposition:

1. `C`: enumerate the current text-bearing semantic surfaces from `Meta/FILEMAP.toml`, then search at least `D5/`, `Blueprint/`, `Library/`, `Problems/`, `docs/develop/theory/`, `Evidence/`, `Chronicle/`, and `Meta/Digestion/`. Search the original wording, translations, historical spellings, synonyms, antonyms, and structural roles such as identity, refinement, factorization, interpretation context, grounding, modality, observer, and relation. Follow references instead of treating a truncated lexical hit list as a completed search.
2. `F`: trace each useful conceptual hit to its formal and provenance owners: exact declarations and statement shapes in `D5/`, rendered meaning and GIDs in `Blueprint/`, active evidence in `Golden/Frozen/accepted/`, and source-to-atom or coverage links in `Meta/Digestion/`. Narrative and theory sources may supply canonical vocabulary, modeling choices, and candidate propositions, but only eligible owner-issued Lean evidence may supply a kernel grade.
3. `M`: use the discovered repository theory to model the input before declaring residual ambiguity. Prefer explicit parameters for tradition, language, context, observer, admissible worlds, modality, or interpretation over silently choosing one meaning. Then construct the concrete or context-indexed `P`, reusable `G`, and applying specialization `S`; only a clause-preserving modeling failure after `C` and `F` may leave the record ambiguous or not formalized.

Search breadth is measured, not asserted. Use the live FILEMAP classification rather than assuming the minimum paths above are exhaustive, and do not call a search complete if output was cut off, a referenced address was not opened, or a semantic synonym/statement-shape pass was skipped. A prose hit never becomes a theorem receipt, but it can prevent an invented abstraction by leading to the repository's existing formal vocabulary.

Formalizability means that a claim can be represented under explicit types, parameters, relations, and hypotheses. It does not mean every wording determines one privileged model, that every defined type is inhabited, or that a formal conditional proves its empirical or metaphysical premises. Reify honest ambiguity as data when the repository supplies that pattern; never manufacture existence, identity, causation, or necessity by definition.

## Generalization bridge

When the assertion is scenario-specific or the user requests generalization, build exactly one bridge before proof construction. The bridge is a proof obligation, not explanatory prose:

1. `P` is the clause-complete concrete proposition fixed from the user's assertion. Preserve every material clause, object, constant, relation, side condition, and empirical premise; no clause may disappear merely because it is inconvenient to generalize.
2. `G` is a reusable Lean theorem that captures the inferential content of `P` by replacing scenario-specific objects and constants with canonical carriers, functions, relations, and explicit hypotheses. Reuse an existing repository or pinned-mathlib abstraction when one owns the shape. A renamed copy of `P`, a theorem whose conclusion is assumed verbatim, or a custom predicate duplicating an existing abstraction is not a generalization.
3. `S` is an exact Lean specialization that applies `G` back to `P` under an explicit substitution map and discharges every resulting hypothesis. Its statement must be exact `P`, or the exact negation of `P` on a refutation branch. `S` may not restate or independently reprove the concrete result; without eligible evidence for both `G` and `S`, generalized evidence cannot grade `P`.

If the input is already stated at the reusable canonical level, record that finding and do not manufacture a tautological `G`; the exact proposition remains the main theorem. Otherwise, every concrete clause in `P` must be accounted for by a parameter, hypothesis, conclusion component, or explicit substitution in the bridge. For conceptual inputs, `G` should quantify over the discovered repository carriers and relations, while `S` supplies the named concepts and any explicit context index. Empirical and metaphysical premises remain premises unless separately discharged by eligible owner evidence.

## Durability routing

After the exact declarations have been checked, apply the first matching route and stop at one. Durability is a disposition over code, separate from the truth outcome assigned in Step 5:

1. `reuse-existing`: an eligible repository declaration already owns exact `G` or canonical `P`. Apply it and cite its `active-frozen` evidence; do not deposit a renamed theorem or convenience wrapper.
2. `discard-thin`: the only new code is `S`, a one-off wrapper, a renamed duplicate, an ornamental definition, or a declaration that fails the `codex-formalize` mathematical-content or deposit-substance gate. Retain it only as `run-local` evidence for the reply and remove the disposable source after reporting it.
3. `deposit-new`: exact `G`, or canonical `P` when no bridge is needed, is a genuine repository miss, compiles with an eligible axiom closure, is reusable beyond the named scenario, and passes every `codex-formalize` fidelity and non-hollowness obligation. Invoke `codex-formalize` in an isolated worktree and let its owners perform formalization, deposit, cover, verification, and publication. Include `S` only when it is independently citable repository mathematics and passes the same gate; scenario-only specialization remains run-local.
4. `open-deposit`: a result already classified as substantive and new cannot yet enter through a current owner-recognized atom, Frontier candidate, or admission route, or the durable owner's capability or execution state machine ends `open`. Preserve the exact statement, proof source, receipts, and named blocking fact as `open`; never bypass the missing route, hand-edit governance data, or silently delete the only recoverable proof artifact.

A successful local compilation is necessary but insufficient for `deposit-new`. Conversely, once a declaration satisfies that route, run-local cleanup is not completion: continue through the owner workflow and report the actual repository or pull-request state. The adapter never copies the deposit procedure; it invokes its owner.

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
- `ambiguous`: provisionally retain a bounded set of materially distinct candidate formalizations without choosing one. Never claim the set is exhaustive without a finiteness proof, and never ask the user to choose. Before this classification can survive Step 2, attempt to turn the variation into an explicit tradition, context, observer, language, modality, or interpretation parameter using repository theory.
- `not-formalizable`: no clause-preserving proposition or explicit model family can be stated even after the complete repository concept search; create no ornamental Lean. Lack of an exact theorem, lack of a keyword hit, or dependence on stated premises does not satisfy this classification.

Separate explanatory prose from assertions. Explanations need no grade; every assertion does.

For each formalizable record, decide whether the generalization bridge is required. It is required when the input names scenario-specific objects or constants, asks what concepts are or how they relate, or asks for a reusable or generalized theorem. An interrogative is not itself graded as an assertion: turn its proposed definitions and relationship answers into separate assertion records, each with its own premises and grade. Record the bridge decision and its clause-level reason; an already canonical reusable statement is the only non-error reason to omit a requested bridge.

Postcondition: every assertion and every material clause is present exactly once, with original wording, classification, clause coverage, and a recorded bridge requirement; no assertion has been dropped or weakened.

### 2. Coordinate and search for reuse

Execute the repository concept search above before fixing the typed echo. Use its discovered vocabulary and formal addresses to execute CLAUDE.md item 11's current owner-defined ordered theorem search. At every stage search the concrete proposition, its negation or counterexample shape, and, when the bridge is required, candidate generalized positive and negative shapes. Search canonical repository and mathematical vocabulary, hypothesis/conclusion structure, imported families, and existing abstractions before introducing local names. Record the verbatim query, where it ran, hit or miss, and the address of every hit. A textual hit discharges nothing until it is exactly reused or applied.

Third-party reuse and admission are owned by specification A17.2. This invocation performs no admission: record an exact third-party hit as provenance, and let Step 5 accept it as kernel basis only if an owner separately issues eligible in-repository evidence.

Invoke specification 11.20.4 for the current SL-028 semantics. This file neither defines its admission effect nor assumes its output is visible; record only output actually received.

Postcondition: each searchable record has complete `C`, `F`, and `M` receipts plus the owner-ordered theorem trace for the concrete and required generalized positive and negative shapes, or the exact blocked stage has an addressed owner-issued `wait-for-capability` fact; every hit has an address and an explicit reuse disposition. No record remains ambiguous or not formalized merely because exact-word or pure-mathematics search missed.

### 3. Fix the exact statement echo

Only after search has fixed canonical domains, types, declarations, and imports, invoke `agents/echo-template.md`; do not copy its fields here. Complete the clause-coverage account against one exact Lean proposition `P`. If the input's meanings vary by an index represented in repository theory, make that index explicit in `P` or create separate bounded candidate records rather than selecting one interpretation. Only ambiguity or modeling failure that remains after `C`, `F`, and `M` gets no exact Lean proposition.

When the bridge is required, also fix exact Lean statements for `G` and `S` plus the substitution map from `G` to `P`. Check that `G` is reusable beyond the named scenario, that none of its hypotheses assumes its conclusion, and that each clause of `P` is accounted for. The statement of `S` must be exact `P`, or its exact negation on the refutation branch, and its planned proof term must apply `G`.

Kernel outcomes attach only to exact `P` or its exact negation, never to the original prose or to a nearby statement.

Postcondition: every eligible record has an owner-shaped exact echo whose clause mapping is complete; each required bridge fixes exact `G`, exact `S`, and a total substitution map back to `P`; context-indexed models expose their indices; only residual ambiguous and not-formalizable records remain explicitly non-kernel branches.

### 4. Stage report-owned declarations

After the owner-ordered search, and only with measured Lean capability, follow the current reuse-before-proof rule in `CLAUDE.md` item 11 in a disposable isolated lane on exactly two occasions: (1) for an exact in-repository or pinned-mathlib hit, create the thinnest honest wrapper that imports and applies the hit; this is reuse, not reproof, and a wrapper that restates or reproves the hit instead of applying it is forbidden; (2) for a genuine miss, create a local proof declaration. When the bridge is required, the main run-local declaration is `G`, and the same managed source must declare `S` by applying `G` under the fixed substitution map. When no bridge is required, declare exact `P` or its exact negation directly. These forms give the canonical report run-local managed declarations it can own and issue declaration receipts for. Select the current build and report doors from the current `make help`; never use a cold bare `lake build`.

This step is run-local staging: do not deposit, freeze, cover, or edit a receipt here. Retain the exact commands, exit codes, diagnostics, pins, canonical report address, and proof source for the later durability decision. A failed attempt is evidence of failure to prove, never evidence that `P` is false.

Postcondition: owner output contains either an exact declaration for `P` or its negation, or, for a required bridge, exact declarations for both `G` and the applying specialization `S`; otherwise it retains the failed attempts and machine diagnostics as facts for Step 5. Every successful new declaration remains available for the durability routing rather than existing only in an already-deleted temporary file.

### 5. Derive outcomes from owner facts

Project outcomes mechanically; never author, select, or downgrade a label. Before applying the ordered rules, discard any purported kernel evidence unless it matches the exact statement and carries either an active Frozen receipt or a successful current `make` door receipt with its exit code, plus the owner-issued declaration receipt and inspector-owned closure contained in the owner-defined standard axiom set. For current evidence, the door receipt, declaration receipt, closure, and report/input attestation must form one bundle from a single production for the current repository inputs: `tools/scripts/lean-report-pair.sh` emits the `input_address` and `report_sha256` join keys, and `tools/scripts/report/lean-report-input.sh verify` verifies the report and current repository input. Never assemble evidence across runs or pins. When a bridge is required, evidence for the original assertion is eligible only if that one bundle contains eligible declarations for both `G` and `S`, and `S` has the exact `P` or exact-negation statement fixed in Step 3; proof of `G` alone grades nothing about `P`. `sorryAx`, any non-standard axiom, a failed command, a missing bridge declaration, or a statement mismatch makes that evidence ineligible. Apply the first matching rule:

1. `not-formalized` when the record is `not-formalizable` and has no Lean statement.
2. `conditional` when the record is `conditional-empirical`, exact `P` is conditional with its named empirical premise undischarged, and eligible owner evidence establishes exact `P`.
3. `proved` when eligible owner evidence establishes exact `P` for any record not matched above.
4. `refuted` when eligible owner evidence establishes the exact negation of `P` for any record not matched above; keep `P` unchanged.
5. `open` otherwise, including an ambiguous record, an unavailable required capability, a provenance-only third-party hit, or no eligible evidence for `P` or its negation.

These rules are a total function over reachable owner-fact states: rule 1 handles the reachable not-formalizable/no-statement state; rules 2-4 handle eligible positive or negative evidence in order; and rule 5 catches every remainder, including ambiguity, unavailable capability, and ineligible evidence. First-match evaluation stops at one rule, so the projected domains are mutually exclusive by construction and exactly one outcome results. In particular, a `conditional-empirical` record whose named empirical premise is discharged cannot match rule 2; eligible evidence for exact `P` matches rule 3 exactly once, yielding `proved`.

`conditional` applies only while the named empirical premise is undischarged. An active Frozen receipt remains reusable without current Lean. Never infer falsity from failure to prove or downgrade a terminal to an informal sink.

Postcondition: every assertion has exactly one mechanically projected outcome, and every formalizable assertion is graded `proved`, `refuted`, `conditional`, or `open`.

### 6. Persist substantive new formalization

Apply the durability routing once to every successful new declaration set. Duplicate search and the `codex-formalize` fidelity and non-hollowness gate decide whether code is substantive; compilation alone does not. When the route is `deposit-new`, invoke `codex-formalize` and follow its current state machine without copying, weakening, or partially simulating it. Use the authoritative atom or owner-issued candidate address it requires. If no current owner can supply such an address, use `open-deposit`; do not invent an atom, append governance data by hand, or treat an untracked file as durable.

Truth grading remains exactly Step 5's function. A deposit failure does not change `proved` to `open` when eligible run-local evidence already proves exact `P`; it changes only the persistence disposition to `open-deposit`. Likewise, an opened or in-flight pull request is not `active-frozen`: report the exact owner-issued state, and call the declaration durable only after the repository owner has actually admitted it.

Postcondition: every successful new declaration set has exactly one durability disposition; every `deposit-new` candidate has been handed to and advanced through the durable owner as far as its state machine permits; every blocked persistence attempt retains an evidence-complete `open-deposit` record.

### 7. Render the reply

For each assertion render the original clause, exact `P` or its explicit absence, the outcome, source or report address, exact commands and exit codes, axiom closure, search trace, and persistence marking. For a required bridge, also render exact `G`, exact `S`, the substitution map, the generalized positive and negative search receipts, and the separate axiom closures for `G` and `S`. For conceptual questions, render the repository concepts and addresses that shaped the model, all explicit context indices, and the boundary between formal consequence and unproved empirical, metaphysical, existential, or interpretive premises. Render the durability route separately from the truth outcome, including the frozen GID, actual pull-request state, run-local pins, or the exact `open-deposit` blocker as applicable.

The outcome vocabulary is closed: `proved`, `refuted`, `conditional`, `open`, `not-formalized`. Do not add an informal assertion grade or any human-review state. Third-party provenance must be visibly distinguished from kernel basis.

Postcondition: the reply is clause-complete, evidence-bearing per assertion, uses only the closed outcome set, exposes every persistence boundary, and makes every required generalization bridge auditable from concrete proposition through reusable theorem to verified specialization.

### 8. Close with persistence accounted

Compare every participating worktree with its pre-run state. For `reuse-existing` and `discard-thin`, remove disposable sources and leave the repository worktree unchanged. For `deposit-new`, preserve and report only artifacts produced or required by the durable owner, including its commits and pull-request state; never clean them away merely to recreate a zero-mutation ending. For `open-deposit`, retain the evidence bundle at its owner-prescribed durable location and report any intentionally dirty worktree exactly.

Postcondition: the answer has been delivered, every truth outcome and durability disposition is explicit, thin staging artifacts are gone, and every substantive new reusable result is either admitted through its owner or preserved with an evidence-complete `open-deposit` continuation.

## Acceptance obligation

At runtime, Step 5's ordered rules are the sole outcome authority. Each assertion record carries the specific address of every owner fact it actually relied on; it never fabricates unused owner addresses.

At skill-change time, before changing this file, the editor must verify that the ordered truth rules remain a total function and that the durability routes remain exhaustive and single-valued. The focused architecture tests are their executable echoes; semantic fidelity remains a **SOFT** obligation, and the FILEMAP owner remains authoritative for repository-policy classification. Failed verification is a defect, not a human-review state.

## Earned hard gates

These are the only hard gates added by this adapter; each names an occurred failure.

- **Honor the owner-issued reuse disposition; never invent a reproof path.** Invoke `CLAUDE.md` item 11 and specification A17.2 (`docs/develop/spec/golden-ledger-repo-spec.md:163`). The occurred incident is the third-party path collapsing into forbidden reproof.
- **Reject a tautological or thin mapping.** Invoke `skills/codex-formalize/SKILL.md`, "Mathematical content" and "Deposit substance," which record seven definitional-tautology cases and the landed thin-deposit case.
- **Do not discard a substantive new reusable proof after local success.** The occurred failure is a valid generalization surviving only in a disposable answer lane, so later questions had to rediscover it. Once `deposit-new` applies, persistence through the existing owner is part of answering, not an optional follow-up.
- **Reject premature ambiguity caused by a narrow repository search.** Complete the `C`, `F`, and `M` path before retaining `ambiguous` or `not-formalizable`; exact-keyword-only, D5-only, and mathlib-only searches are incomplete for conceptual inputs.
- **Never turn representation into existence.** A type, predicate, structure, or context-indexed interpretation supplies a model, not an inhabitant or a proof about reality. Definitions may expose premises; they may not discharge them by construction.
- **Never use a cold bare `lake build`.** Invoke `CLAUDE.md` tool law 3, which records issue #2762's multi-hour cold-lane failure and PR #2764's repair.
- **Treat owner summaries here as non-load-bearing.** Invoke the owner before use; any summary is void on disagreement and may not create an independent rule. Specification revision v7.16 R20 at `docs/develop/spec/golden-ledger-repo-spec.md:877` records the stale `skills/` copy left when a reference-closure sweep missed that directory.
- **Never claim a command result without its exit code.** Invoke `skills/codex-formalize/SKILL.md`, "Process honesty," which records the seat that reported a failed Lean build as green.

## Prohibitions

- No direct deposit, freeze, coverage edit, or receipt edit by this adapter; invoke `codex-formalize` and the canonical doors that own those mutations.
- No second axiom parser, search engine, ledger, or receipt service; `tools/lean-inspector/Inspector.lean` via `make lean-report`, CLAUDE.md item 11, and the frozen ledger own those facts.
- No `requires human review`, `awaiting human`, or equivalent branch; `CLAUDE.md` item 22 owns that prohibition.
- No hedging word in place of a measurement; `CLAUDE.md` section VI owns its typed alternatives.
- No third-party admission by this adapter; specification A17.2 and the durable owner decide it.
- No repository node for a duplicate, thin wrapper, scenario-only specialization, or declaration that has not passed the durable owner's substance gate.

## What this skill does not own

- Search order and `wait-for-capability`: CLAUDE.md item 11.
- Third-party admission: specification A17.2.
- Truth-state syntax: specification 1.4.
- Axiom authority: `tools/lean-inspector/Inspector.lean`, the canonical `make lean-report`, and the owner-pinned standard axiom set.
- Lean build doors: the root `Makefile` as listed by `make help`.
- Freezing, receipts, and coverage: the deposit and cover doors and their existing skills.
- PR mechanics: `make pr-open`.

This skill names each owner and states only the minimum non-load-bearing reading needed to run the workflow. Owners and their live machine output always win; a conflicting local sentence is void.
