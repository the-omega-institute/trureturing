/- GID: D5/S3/ConceptDynamics/History/AppendOnlyAnswerabilityMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/History/AppendOnlyAnswerabilityMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Append-only history preserves every target answerable from the old log. -/

import D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity

/- Library-search audit trail (2026-08-26):
   * Exact current-tree hits `Concept`, `Refines`, `AnswerableTargets`, and
     `answerable_target_monotone` provide the canonical history carriers,
     factorization order, answer set, and refinement monotonicity theorem.
   * The source-specific append projection equation `L_n = p_n ∘ L_(n+1)`
     was searched by `rg` across D5 and the frozen ledger with no exact
     theorem; this module supplies that bridge and applies the existing result.
   * Body-shape search for `AnswerableTargets`, `Refines`, and composition found
     only the imported canonical definitions; no new definition is introduced.
   * Pinned Mathlib search found no stronger append-only answerability theorem;
     `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.History.AppendOnlyAnswerabilityMonotonicity

open D5.S3.ConceptDynamics.Answering.AnswerableTargetMonotonicity
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If the old log is the projection of an append-only extension, every target
answerable from the old log remains answerable from the extended log. -/
theorem append_only_answerability_monotone
    {HistoryIndex OldLog NewLog TargetValue : Type*}
    (oldLog : Concept HistoryIndex OldLog)
    (newLog : Concept HistoryIndex NewLog)
    (projection : NewLog -> OldLog)
    (appendFactorization : oldLog = projection ∘ newLog) :
    AnswerableTargets (Y := TargetValue) oldLog ⊆
      AnswerableTargets (Y := TargetValue) newLog := by
  apply answerable_target_monotone oldLog newLog
  exact ⟨projection, appendFactorization⟩

#print axioms append_only_answerability_monotone

end D5.S3.ConceptDynamics.History.AppendOnlyAnswerabilityMonotonicity
