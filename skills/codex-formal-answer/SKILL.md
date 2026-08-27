---
name: codex-formal-answer
description: Use when answering mathematical, conceptual, philosophical, or metaphysical questions by searching repository theory, completing the missing inference as a reusable Lean theorem, specializing it to the question, and compiling substantive new formalization as tracked project source.
---

# Codex Formal Answer Workflow

## Install

This repository directory is the source of truth for the skill. Install or load the
whole `skills/codex-formal-answer/` directory; an installed copy is only a projection.

## Scope and authority

This skill turns natural-language questions into compiled, reusable project
formalization and an evidence-bearing answer. Repository search supplies vocabulary,
premises, definitions, and reusable lemmas. Search results are not the answer when the
question still requires a cross-concept deduction.

The skill owns the clause-complete `P`/`G`/`S` mapping, the missing inferential step,
and the decision to retain substantive Lean source. Lean source plus a successful
project build is the proof authority for this workflow. It does not wait for or consult
freezing, deposit, coverage, receipt-ledger, or truth-DAG publication state.

Read the following live owners before acting:

- `CLAUDE.md`, especially item 11 and the tool laws.
- `agents/CONTEXT.md` and `agents/echo-template.md`.
- `Meta/FILEMAP.toml`, `Meta/domains.yaml`, and `make help`.
- Existing Lean modules and their Describe sources reached by the search below.
- `tools/lean-inspector/Inspector.lean` only when an axiom-closure report is needed.

## Repository concept search

This is not merely a conventional mathematics repository. It contains formal and
narrative theories of concepts, identity, ontology, metaphysics, agency, ethics,
language, observation, memory, causality, and related domains. Before fixing `P`, run
this repository-first path and retain the queries, result counts, addresses, and
reuse decisions:

1. `C`: enumerate text-bearing semantic surfaces from `Meta/FILEMAP.toml`; search at least `D5/`, `Blueprint/`, `Library/`, `Problems/`, `docs/develop/theory/`, `Evidence/`, `Chronicle/`, and `Meta/Digestion/`. Search the original wording, translations, historical terms, synonyms, antonyms, and structural roles. Follow relevant references and Describe dependencies.
2. `F`: trace useful concepts to exact declarations and statement shapes in `D5/`, their rendered meanings in `Blueprint/`, and pinned library abstractions in `.lake/packages/mathlib/Mathlib/`. Search both the proposed conclusion and its negation or counterexample shape. Reuse exact declarations as lemmas; do not reprove them.
3. `M`: construct exact `P`, reusable `G`, and applying `S` from the discovered carriers, relations, contexts, histories, modalities, observers, and empirical premises. Identify what the existing declarations jointly imply and what inferential link is still missing. A hit list or prose synthesis does not complete `M`.

Search breadth is measured, not asserted. Do not declare the search complete when
output was truncated, a referenced source was not opened, or a semantic and
statement-shape pass was skipped. A prose source can determine vocabulary and model
choice, but only compiled Lean can establish a formal outcome.

Formalizability means a claim can be represented with explicit types, relations,
parameters, and hypotheses. It does not mean the formal model is the one true
interpretation or that its empirical or metaphysical premises hold in reality.

## Generalization bridge

For a scenario-specific or conceptual question, construct exactly one auditable
bridge before proving anything:

1. `P` is the clause-complete proposition that answers the user's actual question. Preserve every material object, relation, qualifier, alternative meaning, and empirical premise.
2. `G` is a reusable theorem over repository-native carriers and relations. It replaces scenario names with parameters and explicit hypotheses while retaining the inferential content of `P`. It must add a consequence not already assumed or merely listed.
3. `S` applies `G` to exact `P` through an explicit substitution map and discharges all formal hypotheses. Its statement is exact `P` or the exact negation of `P`; it may not independently reprove the result.

If the input is already a canonical reusable proposition, record why no bridge is
needed. Otherwise, every clause of `P` must map to a parameter, premise, conclusion,
or substitution in `G` and `S`. Empirical and metaphysical premises remain visible.

## Inferential completion

After search and before implementation, complete the reasoning rather than stopping
at citations:

1. `premise-map`: map every useful repository theorem to the exact premise or intermediate consequence it supplies; expose the remaining empirical, interpretive, and metaphysical premises separately.
2. `G`: derive one clause-complete reusable theorem that composes those ingredients and proves the missing relationship, boundary, equivalence, incompatibility, or trichotomy. Applying existing lemmas is preferred, but the resulting statement must have new inferential content beyond their juxtaposition.
3. `S`: instantiate `G` back to `P`, with a total substitution map from repository concepts to the user's named concepts. Compile both `G` and `S` when the specialization itself carries a formal grade.

A conjunction of unrelated hits, a renamed theorem, a conclusion repeated as a
hypothesis, or definitions chosen so the conclusion is reflexive is not inferential
completion. For a broad question, prefer a theorem that separates interpretations
and proves the boundary between them over forcing one ambiguous yes/no predicate.

## Project source persistence

After compilation, apply the first matching route and stop at one. Persistence is
about useful project code, independent of publication state:

1. `reuse-complete`: one existing declaration already proves the whole `G` or canonical `P`, including every clause and boundary. Cite that `project-source`; do not add a renamed copy. Multiple adjacent hits that still require a deduction do not qualify.
2. `discard-thin`: the only new code is scenario-only `S`, an import wrapper, a renamed duplicate, an ornamental definition, or a theorem whose conclusion is assumed. Keep it as `run-local` build evidence only, then remove it.
3. `persist-synthesis`: a new reusable `G` closes a genuine inferential gap, has nontrivial examples or hypotheses, reuses existing declarations, and compiles without `sorry` or nonstandard axioms. Route it to a canonical module, retain it as `tracked-lean` with a matching canonical `Describe` source, connect it to the project import graph, and verify it with `make lean`; use `make lean-report` only when the answer needs a machine-readable closure.
4. `open-compile`: otherwise, including an unavailable compiler, failed elaboration, unresolved model, or nonstandard axiom closure. Preserve the exact source, command, exit code, and diagnostics as `open`; never report the proposition as proved.

Project compilation is necessary for retained formalization. Thin code does not become
valuable merely because it compiles, and useful synthesis must not be deleted merely
because the natural-language answer can already be written.

## State machine

Follow the steps in order. Do not pass a step until its postcondition holds.

### 0. Measure capabilities

Run `make help`, inspect the current project state, and measure the relevant search and
Lean capabilities. Capability failure is not evidence against any proposition.

Postcondition: every required capability has a command, result, and exit code, or an
explicitly addressed unavailable state.

### 1. Inventory raw clauses

Split the input into assertion records. Preserve each clause and classify it as
`formalizable`, `conditional-empirical`, `ambiguous`, or `not-formalizable`. Turn a
question into candidate answer propositions rather than grading the interrogative.
Model alternative meanings with explicit indices instead of silently choosing one.

Postcondition: every material clause is represented exactly once and each assertion
has a bridge decision.

### 2. Search and model

Execute `C`, `F`, and `M`, then follow CLAUDE.md item 11's reuse-before-proof order.
Search the positive and negative shapes of `P` and `G`. Stop external theorem search
when an exact repository declaration is found, but do not stop inferential completion
unless one declaration closes the complete proposition.

Postcondition: every reused declaration has an address and role in the model, and the
remaining inferential gap is explicit.

### 3. Fix the exact statement echo

Complete `agents/echo-template.md` for `P`, `G`, and `S`. Check clause coverage, total
substitution, non-hollowness, and that no hypothesis assumes the conclusion. Context,
tradition, observer, world, modality, and time indices remain explicit where relevant.

Postcondition: the exact Lean statements and their clause-level mapping are fixed.

### 4. Implement the inferential completion

Route a canonical project module using current repository structure. Write `G` by
applying the strongest exact existing lemmas and proving only the missing composition.
Add concrete inhabited examples or countermodels when they are needed to show that the
theorem is not vacuous. Add `S` when the concrete proposition is itself formalizable.
For retained `G`, add the matching canonical `Describe` source and state the model's
interpretive and empirical limits there. Connect retained source to the project import
graph.

Postcondition: the project contains the smallest substantive theorem that answers the
question, not a catalogue of nearby results.

### 5. Derive outcomes from compiled declarations

Use one successful current `make` build and the exact compiled statements as the
authority. Reject evidence with `sorry`, a statement mismatch, a failed command, or a
nonstandard axiom closure. Apply the first matching rule:

1. `not-formalized` when the record is `not-formalizable` and has no Lean statement.
2. `conditional` when compiled exact `P` is conditional on named empirical or metaphysical premises that remain undischarged.
3. `proved` when the successful build establishes exact `P` for any record not matched above.
4. `refuted` when the successful build establishes the exact negation of `P` for any record not matched above.
5. `open` otherwise, including ambiguity, unavailable compilation, failed proof, or no compiled declaration for `P` or its negation.

These ordered rules are exhaustive and single-valued by first-match evaluation. A
failed proof never implies falsity, and a compiled conditional never discharges its
real-world premises.

Postcondition: every assertion has exactly one outcome from the closed vocabulary.

### 6. Persist project source

Apply the project source persistence route. Keep substantive `G`, its required imports,
and its matching `Describe` source in the repository. Remove thin wrappers and
disposable specializations. Record the final project paths, build command, exit code,
and axiom output or report.

Postcondition: every useful new theorem is compiled project source with a corresponding
human-readable `Describe`; every discarded artifact is demonstrably thin; every
compiler failure remains evidence-complete.

### 7. Render the answer

Lead with the philosophical or mathematical conclusion. Then expose exact `P`, `G`,
`S`, the substitution map, named premises, compiled source address, build receipt,
axiom closure, search trace, and the boundary between formal consequence and real-world
interpretation. Use only `proved`, `refuted`, `conditional`, `open`, and
`not-formalized` as assertion outcomes.

### 8. Close with code accounted

Compare the worktree with its pre-run state. Retain only the canonical substantive
Lean source and required project-import changes. Commit the coherent local unit when
repository policy allows; do not open or advance a pull request unless the user asks.

## Earned hard gates

- Do not answer a complex question with search results alone. The prior failure was a philosophically relevant hit list with no theorem connecting the hits.
- Do not discard a reusable proof after it compiles. The prior failure forced later questions to rediscover the same inference.
- Do not deposit a thin wrapper or renamed theorem. Reuse is still mandatory.
- Do not turn a representation into existence or an empirical fact. Types and models expose premises; they do not prove reality.
- Never use a cold bare Lake command. Use the current `make` doors and report exit codes.

## Prohibitions

- No truth-DAG, frozen-receipt, deposit, coverage, or publication dependency in this answer workflow.
- No search-only response when multiple results still require composition.
- No duplicate theorem, ornamental definition, or scenario-only wrapper retained as project mathematics.
- No outcome without an exact compiled proposition or explicit absence of one.
- No claim that a formal model proves its empirical, existential, or metaphysical interpretation.

The live Lean compiler, project source, and Describe meaning are the evidence boundary
for this skill. Publication and repository-governance workflows are outside its scope.
