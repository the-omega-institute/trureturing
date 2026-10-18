---
name: autonomous-research
description: Carry out one frontier research round in trureturing through AI deep reasoning, preregistration, codex formalization, independent proof and information escape evaluation, literature checks and settlement. Use for research without a supplied result.
---

# One Frontier Research Round

This skill has no authority of its own. `CLAUDE.md` and `docs/develop/spec/golden-ledger-repo-spec.md` prevail; `agents/CONTEXT.md` supplies repository context. Follow `CLAUDE.md` §§3.2–3.3, 3.7, 3.9, 5.11 and `docs/develop/spec/auric_fib_atom_escape_audit_spec.md` §§1, 4, 5, 9.
Complete one research unit: generate a result, preregister, formalize, evaluate, deliver eligible content and settle. Research hit, mathematical truth and content delivery are separate conclusions.

## Generate a result

Ask GPT Pro with `python3 tools/scripts/agent/nyx/nyx.py ask <brief-file> <output-file>`, or another available AI, to reason deeply and directly produce candidate mathematical results. Include both escape tests below, relevant existing statements, assumptions, literature and unresolved boundaries in its brief; do not use atoms or digestion queues as a topic queue.
Every GPT Pro brief includes `https://github.com/the-omega-institute/trureturing` and 「深入思考与推理, 如数学推理按照正式定义定理证明推理」. Follow §5.11's broker and public-evidence rules; oracle proposes and reasons, never verifies.

Require definitions, the complete quantified statement and assumptions, a proof draft with gaps, the proposed non-binding fact and its live role, direct dependencies (GID and `statement_id` for frozen prerequisites), and affected results/consumers. Distinguish proved, assumed and empirical premises.
Require ordinary escape-registration and AURIC `Application` drafts: original theorem occurrence and full dependent telescope, actual source and parameter/state/output families, old/added readouts, task, layers, specialization/reconstruction maps and evidence obligations. Fix the intended information objective and capture or boundary route. The generator need not execute Lean; its complete proposal remains unverified.

Before directed proof, search for reuse: repository declarations including private ones, pinned Mathlib, then admissible third-party Lean libraries. Compare assumptions, quantifiers and actual uses; reuse exact or stronger results rather than reprove or wrap them.

## Two independent escape criteria

A research hit requires **P∧I for the same new result**, each independently evidenced; neither substitutes for the other or creates an admission state.

- **P — proof content:** independent §3.2 evaluation finds `proof_shape: content`, an escape witness on the reduced live derivation path, normal admission and §3.3 use obligations satisfied. Ordinary four-slot registration retains its separate §3.9 verdict.
- Expand local aliases, new helpers, tactics and definitional equalities up to frozen/pinned premises. Instantiation, premise substitution, logical projection/recombination and normalization alone are bind-only. An intermediate witness must occur in the elaborated dependency closure, escape those operations, be neither definitionally equivalent to nor an alias/restatement of the conclusion, and survive reduction/dead-term removal on its live path; a dispensable dependency does not qualify. The conclusion itself may instead arise directly from a non-binding computation, construction or estimate; do not invent an intermediate.
- **I — task information:** a source-faithful compiled `Application` and its normal compiler-report `fib_analysis`, consumed through the existing material/source custody chain, establish the preregistered nontrivial information objective for the fixed actual task. The joint kernel identifies lawful states when all fixed readouts agree. Use either route:
  - **Capture:** prove genuine unique capture or strict refinement of the old joint kernel, with lawful witness states in the same source/parameter fiber, and prove that the distinction affects the fixed task.
  - **Boundary:** prove a nontrivial task limitation or sufficiency result: same old readouts with different task answers, task constancy/nonconstancy on observation fibers, or an association/continuation residual bound. Preserve domain, quantifiers and task correspondence; positive unique capture is not required.

Bind all source/readout/task/layer fields to the same actual implementation and original occurrence, preserving its full telescope and explicit specialization/reconstruction. Verified correspondence needs this client's Lean proof terms, accepted axiom closure and current compiler/source binding evidence; interface compilation or a convenient true substitute is insufficient.

Run three controls on that same lawful source and task: identity readout, duplicate readout and unrelated coordinate. Report their actual readings and scope, including zeros or acquisition gaps; tautological separation, repetition or task-irrelevant refinement counts as no new result. Do not change the source/task to improve a control.

Report kernels, unique capture, initial and collapsed layers, and final unresolved pairs as acquired. Finite rates need a certified complete finite arena with N>1; dependent/infinite domains may retain qualitative structure. Native FIB coordinates/residuals need their actual source/reader/continuation bridges; arbitrary theorems do not inherit `native_execution`.
Preserve `unknown`, `unavailable` and `not-applicable` with their precise acquisition reasons, never replace them with zero. The standalone `make -C tools auric-fib-analysis` checks supplied-table arithmetic, authenticates neither source nor Application, and cannot establish I.
Do not use δ=0 or either ε endpoint as an admission/novelty gate. Do not combine proof escape, information, surprise, cost or research value into a total score, ranking proxy or invented value function.

## Preregister before directed proof

After exploratory generation and initial duplicate/literature screening, before any directed probe, computation, solver attempt or Lean implementation, use a research-unit issue. Record the complete candidate, event/assumptions, proposed non-binding fact/live path, admission/use basis, information route/objective, domain, readouts, task and layer order, success/refutation/stopping criteria and deadline.

Keep generator, predictor, solver and independent evaluator roles separate; no seat evaluates its own proposal or implementation. Give fresh isolated prediction seats only the event and assumptions/quantifiers, without the generated proof, witness, Application solution, probe/solver output, inherited conversation or access to solution-bearing material. Predictions estimate truth, not content or research value.
Obtain a codex prediction and attempt at least one attributable non-GPT-family prediction; record actual model families. If unavailable, record the capability failure and retain only genuine predictions, never invent probabilities or diversity. Oracle may generate/reason/predict; all validation, including fidelity and proof shape, belongs to codex-cli under §5.11.

Use `tools/scripts/agent/research_readouts/README.md` as the strict block contract. Append one unchanged comment with a fenced `research-prereg-v1` block: exactly `event`, `deadline`, `scoring_rule`, `surprise_threshold`, `predictions`; each prediction has exactly `seat`, `model_family`, `event`, `probability`.
Use exact event text, UTC timestamps, binary Brier version 1 and valid numeric probabilities/threshold; `[]` records missing predictions. Registration time is REST `created_at`, with `updated_at == created_at`. Read back the complete carrier and frozen predictions before recording substantive execution start, at or after registration and before the deadline.
Keep candidate detail, P/I objectives, source/readout/task/layer contracts, controls and conclusions outside strict JSON blocks. Each issue has at most one preregistration and one terminal block across body/comments; blocks belong in unchanged comments, not the issue body. Changed events, witnesses or information targets require a fresh preregistered issue preserving the old settlement, never edits or replacement blocks.

Before writing to GitHub, check the complete existing comments for the same comment and reuse it instead of duplicating it.
An already terminated unit is not researched again, regardless of issue open/closed state; use its terminal or owning settlement evidence. Further mathematics requires a fresh preregistration linked to the old result and boundaries.

## Formalize and evaluate

Codex follows `skills/codex-formalize/SKILL.md` for D5 Lean, Blueprint Scribe, Reg, Application, atom overlap checks, freezing/coverage and independent reviews. A theory volume or ingestion is not a prerequisite. Atom lookup is downstream of generated results.
Use the canonical make doors, including `make lean-report-scoped LEAN_TARGETS="<nonempty dotted modules>"` for the delivered modules, utility inputs and imports, and `make gate BASE=<40-hex-comparison-base>`. Inspect actual exits and current bindings; only Lean kernel and existing judges establish verified truth/check status, not AI proof prose or a readout count.

A fresh independent codex evaluator checks the exact event-to-Lean mapping, live-path P, admission/use, ordinary registration status, and I from custody-checked `fib_analysis` against the original information contract. Report P and I separately with evidence or named gaps; missing I does not refute a proved mathematical event.
Known or wholly bind-only internal results go to reuse with no filler Lean. Consumed bind-only helpers remain allowed under §3.2 but provide no escape content. The external named-open-problem exception follows §§3.2/3.6, including preregistered source/tier/literature checks; bind-only admission there does not establish P. After two consecutive other bind-only targets, change representation under §3.2.
Do not alter judges, weaken the statement or add irrelevant dependencies to obtain a verdict. Retain successful ordinary registration; disclose unfinished registration with its linked issue under §3.9 without calling it `declared_validated`.

Eligible verified results complete normal formalization delivery in a content PR through the owning workflow, with its required checks/reviews and disclosures. Missing I alone does not prevent otherwise admissible content delivery; a mathematical terminal does not establish delivery completion.

## Literature due diligence

Perform §3.7 literature due diligence when writing formal statements/narratives and before novelty claims or delivery, using codex networking and the §5.11 reading routes: Claude Code `WebSearch`/`WebFetch` or GPT Pro search for legally readable originals. Inspect original text, version and theorem conditions with an executable carrier; oracle summaries/excerpts are leads, never verification.
Keep minimal scoped source findings: `literature-attested` for known results, `repo-derived` for repository derivations, `suspected-novel` only after serious scoped search and original-source checks found no prior result. Unread sources remain explicit unverified gaps; search misses prove no global originality.

## Settle the unit

At its deadline or registered stopping trigger, settle from obtained evidence under the original criteria. Separate proved/refuted mathematics, invalid attempts and unresolved obstacles from P/I research hit and content-delivery status. An incomplete attempt proves neither answer; no eligible candidate means a bounded no-result conclusion, not filler Lean.

Append at most one unchanged comment with a fenced `research-terminal-v1` block under the README contract: exactly `event`, `execution_started_at`, `status`, `settled_at`, `evidence`, `shape_evidence`. Preserve the preregistered event; status is `proved`, `refuted`, `invalid` or `unresolved`, with settlement time null for invalid/unresolved.
Evidence references contain exactly `url` and a verbatim nonempty `excerpt` from existing settlement/obstacle evidence. Shape evidence references the independent evaluator's exact excerpt `proof_shape: content` or `proof_shape: bind-only`, or is null when absent; invalid/unresolved require null. No substantive execution means no invented start or terminal: record that disposition outside the blocks.

Run `make -s -C tools research-readouts ISSUES="<issue numbers>" AS_OF="<UTC cutoff>"`; it reads carriers, not writes blocks. The cutoff must reach included metadata and, for unresolved z=1 readings, the original deadline. Record actual exit/named failures; let the tool compute five-mode counts, X/Y/Z, denominators, scores, coverage and missingness.
Missing predictions never yield surprise; unresolved is not false; structural zeros are not measured predictability. Brier loss measures prediction error, not information/value. Readouts supply neither residual sufficiency nor f, E[f], rankings or calibration.

Leave conclusions, separate P/I evidence/gaps, control/literature findings, unresolved boundaries and an exact proposed successor in the unit issue: fully quantified statement/assumptions, source-result links and checks still needed, or why none was identified. A successor needs its own preregistration, admission/use and P/I evidence.
Retain only formal results, necessary sources and conclusions in their existing owners under §2.10; link rather than duplicate them. Experimental programs/data/reports belong in the private experiments repository. Do not commit prompts, transcripts, snapshots, command streams, aggregate scoreboards or a second result store.
