---
name: codex-formal-answer
description: Use when answering mathematical, conceptual, philosophical, or metaphysical questions through repository-first scientific reasoning, a clause-complete formal bridge, and an ordinary conversational answer.
---

# Codex Formal Answer Workflow

## Install

This repository copy is the single source of truth for `skills/codex-formal-answer/`; any installed copy is a projection of it.

## Scope and authority

This file is Codex-specific packaging of repository obligations; it has no authority of its own. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification; `CLAUDE.md` is the invariant frame governing how work is done; and `agents/CONTEXT.md` is the finite-context map and routing aid, not an authority above the specification. Live harness output is the decisive judge of fact about the current tree. If this file disagrees with any of them, they win and this file is the bug.

This skill produces two things. An internal assertion record for the current run always exists, including when no Lean is written. The default public product is an ordinary conversational answer rendered from that record. The internal record carries the clause inventory, `P`/`G`/`S` bridge, premise map, evidence, outcomes, conditions, and derivation; Step 7 directs the public answer to be drafted only from that record and subjects it to a bounded worker audit. That audit reduces leakage but cannot guarantee that natural-language strength never exceeds the register.

codex-formalize owns digestion atoms and their deposit and coverage workflow. This skill owns the user's clause-complete `P`/`G`/`S` bridge, inferential completion, assertion register, and renderer. Do not import freezing, deposit, coverage, receipt-ledger, or truth-DAG publication machinery. Leave a repository mutation only when Step 2 selects a new-`G` compile route and Step 6 retains substantive canonical source.

## Read first

- `CLAUDE.md`, especially items 4, 5-double-prime, 6, 11, 15, 18, and 20-prime, plus section VI's ban on hedge-words substituting for measurement.
- `agents/CONTEXT.md` and `agents/echo-template.md`.
- `docs/develop/spec/golden-ledger-repo-spec.md`, `Meta/FILEMAP.toml`, `Meta/domains.yaml`, and `make help` when repository mutation is in scope.
- Existing Lean declarations and Describe sources reached by Step 2; read `tools/lean-inspector/Inspector.lean` only when an axiom-closure report is material.

## Method anchors

`CLAUDE.md` item 5-double-prime solely owns the meanings of the eight disciplines and marks their use as agent reasoning as analogical. The registry below supplies only grep-resolvable frozen declaration addresses; it does not restate theorem content or assert a one-to-one discipline/declaration mapping. The pre-commitment discipline has no single frozen declaration and is carried by the existing machinery named in `CLAUDE.md`. The Pareto discipline has two anchors.

- `lookup_copy_zero_loss_and_nonanticipating_failure` - `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure.lean`
- `blind_residual_charge_decomposition` - `D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition.lean`
- `budget_envelope_infimum_and_limit` - `D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion.lean`
- `append_only_old_settlement_unchanged` - `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/TargetChangeSettlementConservation.lean`
- `pareto_weak_reflexive_transitive` - `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder.lean`
- `gain_difference_self_zero_and_cocycle` - `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle.lean`
- `dependency_closure_admission_antitone` - `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/DependencyClosureAdmissionAntitone.lean`
- `spectrum_commitment_local_settlement` - `D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentSettlement.lean`

## State machine

Follow the steps in order. Do not pass a step until its postcondition holds.

### 0. Fix the answer commitment

Before searching, record the candidate answer propositions, what would count as answering each one, what would refute each one, and the bounded stopping and settlement criteria. Apply the pre-commitment discipline from `CLAUDE.md` item 5-double-prime; do not revise the criteria to fit evidence already seen.

Postcondition: the answer, refutation, and stop conditions are fixed before evidence collection.

### 1. Inventory raw clauses

Split the input into assertion records and give each assertion a stable key that survives later revision. Preserve every material object, relation, qualifier, alternative meaning, empirical premise, and metaphysical premise exactly once. Turn a question into candidate truth-valued answer propositions rather than grading the interrogative. Model alternative meanings with explicit indices instead of silently choosing one.

Classify each assertion from its clause shape as `formalizable`, `conditional-empirical`, `ambiguous`, or `not-formalizable`. It is formalizable exactly when a truth-valued `P` can be stated with explicit types, relations, quantifiers, and hypotheses. Fix the classification here; proof difficulty, elapsed effort, convenience, and compiler availability cannot later change it. A formal representation does not establish that its empirical, existential, metaphysical, or interpretive premises hold in reality.

Postcondition: every material clause has one stable-keyed record, one fixed classification, and a candidate exact `P` or an explicit reason no exact `P` can yet be stated.

### 2. Search and model

Execute `C`, `F`, and `M` in that order and retain queries, result counts, addresses, and reuse decisions.

1. `C`: enumerate text-bearing semantic surfaces from `Meta/FILEMAP.toml`; search at least `D5/`, `Blueprint/`, `Library/`, `Problems/`, `docs/develop/theory/`, `Evidence/`, `Chronicle/`, and `Meta/Digestion/`. Search original wording, translations, historical terms, synonyms, antonyms, and structural roles; follow relevant references and Describe dependencies.
2. `F`: trace useful concepts to exact declarations and statement shapes in `D5/`, rendered meanings in `Blueprint/`, and pinned abstractions in `.lake/packages/mathlib/Mathlib/`. Search the proposed conclusion, its negation, and counterexample shapes. Follow `CLAUDE.md` item 11's repository, mathlib, third-party, local-proof order. Stop external theorem search at an exact repository hit, but continue inferential completion unless that one declaration closes the complete proposition. Reuse and apply the strongest exact declaration that supplies the needed claim; never reprove it or add a renamed copy. A weaker exact hit does not license rebuilding what a stronger declaration already supplies.
3. `M`: construct the candidate `P`, reusable `G`, and applying `S` from discovered carriers, relations, contexts, histories, modalities, observers, and premises. Map what the declarations jointly imply and name the remaining inferential gap. A hit list or prose synthesis does not answer a complex question that still requires composition.

Do not call search complete when output was truncated, a referenced source was unopened, or either the semantic or statement-shape pass was skipped. Prose may choose vocabulary and model boundaries; only compiled Lean can establish a formal outcome.

Invoke the remaining disciplines from `CLAUDE.md` item 5-double-prime here. Bind lookup-copy, blind-residual, budget-envelope, Pareto/gain, and dependency-closure admission to `C`/`F`/`M` route evaluation, and record each application and result; Step 5 owns append-only and local settlement.

Search chooses only the implementation route: reuse one exact compiled declaration, compile one new load-bearing `G`, or produce no Lean. Failed proof, unavailable compiler, elapsed effort, and convenience do not revise Step 1; they leave the internal result unsettled.

Across all routes, record an unavailable required capability with its command and result or an explicit unavailable-state note; never silently treat it as completed work.

Postcondition: every source has a role and trust status, the inferential gap and ambiguity class are explicit, and exactly one implementation route is selected without changing formalizability.

### 3. Fix the exact statement echo

Complete `agents/echo-template.md` separately for every `formalizable` assertion: exactly one auditable bridge per `formalizable` assertion key, not one bridge per run. Do not retain competing bridges for the same assertion key.

1. `P` is the clause-complete truth-valued proposition answering the user's actual question.
2. `G` is a reusable theorem over repository-native carriers and relations. It replaces scenario names with parameters and explicit hypotheses, retains the inferential content of `P`, and adds a consequence not already assumed or merely listed.
3. `S` applies `G` to exact `P` through a total explicit substitution map and discharges every formal hypothesis. Its statement is exact `P` or exact negation of `P`; it does not independently reprove the result.

If `P` is already canonical and reusable, use `G := P` and an identity substitution as `S`; there is no bridge exception. Map every clause of `P` to a parameter, premise, conclusion, or substitution. Keep context, tradition, observer, world, modality, time, and empirical or metaphysical premises explicit where relevant.

For every `not-formalizable` assertion, record the Step 1 reason no exact `P` can yet be stated and proceed directly to Step 5 without manufacturing a `P`/`G`/`S` bridge.

Postcondition: each `formalizable` assertion key has exactly one fixed `P`/`G`/`S` bridge, clause coverage, and total substitution map, with no hidden premise and no hypothesis that assumes the conclusion; each `not-formalizable` key has its recorded reason and no bridge.

### 4. Implement the inferential completion

Implement the missing composition through this ordered completion:

1. Build a `premise-map` that maps every useful declaration to the exact premise or intermediate consequence it supplies and lists empirical, interpretive, and metaphysical premises separately.
2. Use `G` to implement only the missing composition; a conjunction of unrelated hits, a renamed theorem, a conclusion repeated as a hypothesis, or definitions chosen to make the conclusion reflexive is not completion.
3. Use `S` to apply `G` to exact `P`; for a broad question, separate interpretations and prove their boundary instead of forcing an ambiguous yes/no predicate.

On the reuse route, carry out Step 2's reuse decision and write no new Lean. On the new-`G` compile route only, run `make help`, inspect current project structure, and measure compiler capability with current `make` doors and exit codes; never use a cold bare Lake command. Route the smallest canonical module, prove only the missing composition, and add concrete inhabited examples or countermodels when needed to establish non-vacuity. Compile `G` and any formally graded `S`. On the no-Lean route, write no ornamental definition or scenario wrapper.

Capability failure is not evidence for or against `P`. A failed or unavailable compile leaves the formal result unsettled.

Postcondition: the record contains either an exact reused declaration, the smallest substantive compiled synthesis, or explicit evidence for no formal result; search results alone never masquerade as the missing inference.

### 5. Settle outcomes and freeze the answer register

Use one successful current `make` build and the exact compiled statements as the authority for any formal result. Reject evidence with `sorry`, a statement mismatch, a failed command, or a nonstandard axiom closure. Apply the first matching rule:

1. `not-formalized` when the record is `not-formalizable` and has no Lean statement.
2. `conditional` when compiled exact `P` is conditional on named empirical or metaphysical premises that remain undischarged.
3. `proved` when the successful build establishes exact `P` for any record not matched above.
4. `refuted` when the successful build establishes the exact negation of `P` for any record not matched above.
5. `open` otherwise, including ambiguity, unavailable compilation, failed proof, or no compiled declaration for `P` or its negation.

These ordered rules are exhaustive and single-valued by first-match evaluation. A failed proof never implies falsity, and a compiled conditional never discharges its real-world premises.

Emit one immutable internal settlement record per material assertion. It contains a unique record id, the stable assertion key, an explicit initial `active` status, the exact proposition, outcome, every undischarged condition, the unsettled reason where applicable, whether the claim is a formal result or a judgment, and the maximum permitted public claim. Set that maximum from the outcome: `proved` permits exact `P`; `refuted` permits exact negation of `P`; `conditional` permits only the consequent under every undischarged condition; `open` permits neither `P` nor its negation; and `not-formalized` permits only the recorded nonformal judgment, never a formal-grade claim. No outcome is allowed without an exact compiled proposition or an explicit record of its absence. Apply the local-settlement duty from `CLAUDE.md` item 5-double-prime; do not leave an elapsed task disguised as still progressing.

After any revision of `P` or `G`, append a validity delta that explicitly assigns `void` to each superseded active record for that assertion key, names every earlier settlement that still stands, and append a replacement settlement as `active`. The latest status assignment is the record's effective `active` or `void` status; never overwrite a record or delta, and keep exactly one active settlement per key.

Postcondition: every assertion key has exactly one active record with one outcome and one maximum permitted claim, while every record has an explicit effective `active` or `void` status in the append-only validity history.

### 6. Persist project source and account for the worktree

Apply the first matching route and stop at one:

1. `reuse-complete`: one existing declaration already proves the whole `G` or canonical `P`, including every clause and boundary. Cite that `project-source` and stop persistence. Multiple adjacent hits that still require a deduction do not qualify.
2. `discard-thin`: the only new code is scenario-only `S`, an import wrapper, an ornamental definition, or a theorem whose conclusion is assumed. Keep it as `run-local` build evidence only, then remove it.
3. `persist-synthesis`: a new reusable `G` closes a genuine inferential gap, has nontrivial examples or hypotheses, reuses existing declarations, and compiles without `sorry` or nonstandard axioms. Route it to a canonical module, retain it as `tracked-lean` with a matching canonical `Describe` source that states the model's interpretive and empirical limits there, connect it to the project import graph, and verify it with `make lean`; use `make lean-report` only when the answer needs a machine-readable closure.
4. `open-compile`: otherwise, including an unavailable compiler, failed elaboration, unresolved model, or nonstandard axiom closure. Preserve the exact source, command, exit code, and diagnostics in the current-run record as `open`; never report the proposition as proved.

Compare the worktree with its pre-run state. Retain only substantive canonical source and required import changes; remove thin artifacts and disposable specializations. Useful synthesis is not discarded merely because prose can answer, and thin code does not earn retention by compiling. Commit the coherent local unit only when repository policy and the user's request allow; never open or advance a pull request unless requested.

Emit an internal `side_effects` record containing the final project paths, the exact build command and exit code, the axiom output or report or an explicit reason none was produced, any other verification commands and exit codes, whether anything was committed, and the plain verification result. If nothing was written, record that fact and an empty path set without inventing a mutation.

Postcondition: persistence is settled, the final tree is accounted for, every discarded artifact is demonstrably thin, every compiler failure is evidence-complete, and `side_effects` describes the state that Step 7 will report.

### 7. Render the plain answer

For this skill's output, default to ordinary conversational prose. By default omit `P`/`G`/`S` labels, GIDs, proof-provenance module paths, build receipts, axiom closures, search traces, and the outcome-vocabulary words. This is not a repository-wide register policy.

The procedure directs the renderer one-way from the immutable Step 5 register to prose to reduce epistemic-strength leaks; it does not make the renderer strength-monotone. The register is its only epistemic input; it may not draft claims afresh from search hits, `G`, or `S`. Draft ordinary prose freely without a phrase table, then ask what a competent reader would take away from every heading, lead, body paragraph, and final sentence, including what is implied rather than stated, and translate that takeaway into propositions. Assertive sentences, presuppositions, definite descriptions, rhetorical questions, imperatives, sentence fragments, and conventional implicatures are non-exhaustive examples, not a closed list. Match each epistemic proposition to the unique active Step 5 record for its stable assertion key, never to a void record, and ask whether that active record entails it with no hidden premise. Match each repository-action proposition to the Step 6 `side_effects` record. If the competent-reader takeaway is unmatched or exceeds the active record's maximum permitted claim, reject and redraft it. For this audit, communicating any proposition stronger than an active `open` record's `P` counts as asserting `P`. Do not emit the answer while the worker has identified any stronger or unmapped item.

Enforce these scope rules during that audit:

- Put every material condition in the same sentence or grammatical scope as its consequent; a detached disclaimer does not count.
- For an unsettled proposition, redraft any wording from which a competent reader would take away `P` or its negation, including after "my judgment is." The forms named above are examples, not the boundary. Ground any practical recommendation separately and say that it does not settle the question.
- For a mixed summary sentence, qualify, split, or delete it until it does not exceed its weakest load-bearing clause. A clause is load-bearing when removing it changes which active record the sentence maps to.

Treat each active record's maximum permitted claim as the drafting ceiling: whenever the competent-reader test identifies an excess, reject and redraft it. The competent-reader takeaway, natural-language entailment, and no-hidden-premise checks are worker judgments, not decidable procedures; this prompt-level audit reduces the leak surface and blocks identified channels, but unbounded pragmatic conveyance means it cannot guarantee strength preservation. There is no lint behind it; do not claim machine-level enforcement.

Default suppression yields when it would hide a material condition, model boundary, unresolved ambiguity, compiler or axiom limitation material to the answer, persistent repository mutation, or an audit record requested for proof review, reproduction, debugging, or challenge. Expose the minimum formal detail the answer needs. When a formal predicate's ordinary-language name differs materially from its formal content, state in ordinary words what the term actually means there; a formal symbol or bare "within the model" does not suffice. Include excluded ordinary readings and material observer, world, and time indices whenever they change the answer. When the user requests the full record, show the current run's record; do not promise indefinite storage or later retrieval.

If Step 6 retained source, add one ordinary sentence naming every changed path, whether it was committed, and the plain verification result. This action disclosure is a narrow exception to suppressing proof-provenance paths and receipts. If nothing was written, claim nothing about repository mutation.

Postcondition: the answer reads like normal conversation; the worker has mapped its competent-reader takeaways, redrafted every strengthening or unmatched item the audit identified, kept all material limits visible, and accurately disclosed repository side effects. This records completion of the bounded judgment, not a guarantee that no pragmatic strengthening remains.
