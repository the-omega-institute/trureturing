---
name: autonomous-research
description: Use deep AI reasoning to produce frontier mathematics, formalize it, audit proof and AURIC FIB information escape, and record the next precise boundary.
---

# Frontier research and audit improvement

This skill has no authority of its own. `CLAUDE.md`, the applicable specification, and live compiler/judge
output prevail. It has two loops: research, then evidence-based audit improvement. A theory volume or
digestion queue is never a topic queue or prerequisite.

## Research loop

1. Ask GPT Pro or another available AI to reason deeply and directly propose a result with
   `python3 tools/scripts/agent/nyx/nyx.py ask <brief-file> <output-file>`. The brief includes
   `https://github.com/the-omega-institute/trureturing` and `深入思考与推理, 如数学推理按照正式定义定理证明推理`.
   The domain is open: seek something not previously seen that is worth doing, rather than selecting a topic.
2. Require definitions, the complete quantified statement, all assumptions, proof/derivation and gaps,
   proved/assumed/empirical premises, frozen dependencies (`GID`, `statement_id`), affected consumers,
   and a proposed non-binding fact with its live path. The oracle proposes and reasons; it never verifies.
3. Require an ordinary escape-registration draft and an AURIC `Application` for the same theorem occurrence:
   full dependent telescope; actual source, parameter/state/output families; source and specialization/
   reconstruction bridges; old/added readouts; task and layer order; and evidence obligations. Fix a
   nontrivial information objective and a capture or boundary route. AI prose remains unverified.
4. Before directed proof, search repository declarations (including private ones), pinned Mathlib, then
   admissible third-party Lean libraries. Compare assumptions, quantifiers and consumers; reuse an exact or
   stronger result instead of wrapping or reproving it. Already terminated units are reused. A changed event,
   witness or information target needs a fresh preregistered unit preserving the old settlement.
5. Before any directed probe, computation, solver attempt or Lean implementation, record the candidate,
   assumptions, proposed live path, admission/use basis, P/I objectives, domain, readouts, task, layers,
   success/refutation/stopping criteria and deadline in the unit issue. Keep generator, predictor, solver and
   independent evaluator separate. Prediction seats see only event and assumptions/quantifiers; obtain a
   Codex prediction and attempt an attributable non-GPT-family prediction, recording capability gaps honestly.
6. Follow `tools/scripts/agent/research_readouts/README.md`: one unchanged `research-prereg-v1` comment with
   exactly `event`, `deadline`, `scoring_rule`, `surprise_threshold`, `predictions`; use UTC, binary Brier
   version 1, valid numeric probabilities, and `[]` for missing predictions. Across body/comments allow at
   most one preregistration and one terminal block. Before writing GitHub, check complete comments for the same
   comment. Keep candidate details outside the strict block.
7. Follow `skills/codex-formalize/SKILL.md` directly for D5 Lean, Blueprint Scribe, Reg, `Application`,
   and normal formalization delivery. Use `make lean-report-scoped LEAN_TARGETS="<nonempty dotted modules>"`.
   Kernel checks, accepted axiom closure and current source binding decide truth; formalization may fail, and
   its concrete diagnostics go back to the reasoning side. The formalization lane obeys “形式化不改判官”.
8. A research hit requires **P∧I for the same result**, independently evidenced. P requires an independent
   §3.2 `proof_shape: content` judgment, a non-binding witness on the reduced live path, and §3.3 admission/
   use obligations. Instantiation, projection, premise substitution, normalization, aliases and dead helpers
   are bind-only; the witness survives reduction and is neither a restatement nor dispensable. §3.9 remains separate.
9. I requires a source-faithful compiled `Application` and compiler-report `fib_analysis` through the existing
   material/source custody chain, establishing the fixed task objective. Capture proves strict old-kernel
   refinement with lawful same-fiber states whose distinction changes the task. Boundary proves a nontrivial
   limitation, sufficiency, task constancy/nonconstancy on a fiber, or association/continuation residual bound.
   P and I are reported separately; neither is a score or admission state.
10. Bind source, readout, task and layer fields to one implementation and occurrence; preserve full telescope,
    specialization, reconstruction, Lean terms, axiom closure and compiler/source evidence. Run identity,
    duplicate and unrelated-coordinate controls on that source/task. Report actual readings and scope,
    including `unknown`, `unavailable`, `not-applicable`, zeros and precise acquisition gaps; tautological,
    repetitive or task-irrelevant controls yield no result. `make -C tools auric-fib-analysis` checks tables only.
11. For a FIB-capable occurrence, report layers separately: microscopic atom, seam, guard, reply, state/kernel,
    continuation residual, initial/collapsed layers and final unresolved pairs; macroscopic five-mode law and
    pyramid `x/y/z`, `X/Y/Z`, `w`, `κ/Δ`, `J_f`, and the specified continuation or micro-escape relation.
    Keep source law, sample and native continuation distinct. Native coordinates require a real source/reader/
    continuation bridge. Existing examples are `Reg/D5/S0/Diagonal/PigeonholeFiber.lean`,
    `Reg/D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber.lean`, and
    `Reg/D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.lean`, consumed by
    `tools/lean-inspector/fib_analysis.py`; arbitrary theorems do not inherit FIB meaning.
12. Perform §3.7 literature due diligence through §5.11 routes before novelty claims. Inspect readable originals,
    versions and theorem conditions with an executable carrier; oracle summaries are leads. Use only scoped `literature-attested`, `repo-derived` or `suspected-novel` labels, and keep unread sources as explicit gaps.
13. Settle at the registered deadline or stopping condition, separating proved/refuted mathematics, invalid
    attempts, unresolved obstacles, P, I and delivery. Append at most one unchanged `research-terminal-v1`
   comment using the README's exact keys (`event`, `execution_started_at`, `status`, `settled_at`, `evidence`,
   `shape_evidence`); status is `proved`, `refuted`, `invalid` or `unresolved`, and invalid/unresolved use
   null settlement. Evidence entries are exact `url`/verbatim nonempty `excerpt` references; shape evidence
   is the evaluator's exact `proof_shape: content` or `proof_shape: bind-only`, or null. Then run
   `make -s -C tools research-readouts ISSUES="<issue numbers>" AS_OF="<UTC cutoff>"`.
    Missing predictions are not surprise; unresolved is not false; Brier/readout values are not value, ranking, calibration or
    sufficiency. Leave separate evidence/gaps, controls, literature, boundary and an exact successor in the unit issue; retain
    only formal results, needed sources and conclusions under §2.10.

## Audit improvement loop

14. After each unit, record evidence-backed audit improvement candidates in the existing issue: missing escape or
    FIB readings and causes (fixed adapters, absent bridges, unavailable readers), non-machine semantic steps such
    as proof shape, trivially inflated readings, and specification/implementation mismatches. Keep P and FIB readouts
    separate; never invent a total score, threshold or admission gate.
15. When the same concrete deficiency recurs, improve its adapter, source bridge, readout, analyzer or judge in an
    independent tools/judge lane under `CLAUDE.md` §§8.12 and 8.14. The research/formalization lane does not
    modify `tools/**`, `.github/**` or judge surfaces; it reports exact evidence and continues with the boundary.
    Do not add machinery for hypothetical inputs.
16. If the deficiency is in this procedure, revise this skill from recorded evidence. If it requires an owner-
    authorized rule change, record the concrete case for the normal `CLAUDE.md` or specification review path. Every
    improvement states the observed failure, smallest change, test reading and remaining unknown, and never rewrites a prior settlement.
