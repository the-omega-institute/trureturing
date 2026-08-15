/- GID: D5/S3/ObserverMemory/Prediction/FeedbackCompletionNaturality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FeedbackCompletionNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Projected-state feedback preserves a family of semiconjugate updates. -/

import Mathlib.Logic.Function.Conjugate

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hit: `Function.Semiconj.comp_eq` converts the
     pointwise semiconjugacy proved below into the required function equality;
     it is imported and applied.
   * Loogle also returned `Function.Semiconj.eq` and
     `Function.semiconj_iff_comp_eq`; a shaped family query did not elaborate.
   * LeanSearch returned generic semiconjugacy and flow results, but no theorem
     for a transition family under projected-state-dependent feedback.
   * Repository and formalization-receipt searches found no equal or stronger
     declaration covering this closed-loop statement.
-/

namespace D5.S3.ObserverMemory.Prediction.FeedbackCompletionNaturality

/-- If every update in a control-indexed family is semiconjugate through a
projection, choosing the control by feedback from the projected state preserves
that semiconjugacy for the resulting closed-loop updates. -/
theorem feedback_completion_naturality
    {Y Z U : Type*}
    (update : U -> Y -> Y) (completedUpdate : U -> Z -> Z)
    (projection : Y -> Z)
    (hintertwine :
      forall u, Function.Semiconj projection (update u) (completedUpdate u))
    (feedback : Z -> U) :
    projection ∘ (fun y => update (feedback (projection y)) y) =
      (fun z => completedUpdate (feedback z) z) ∘ projection := by
  apply Function.Semiconj.comp_eq
  intro y
  exact hintertwine (feedback (projection y)) y

/-- Boolean negation as projected feedback witnesses satisfiable hypotheses. -/
example :
    (id : Bool -> Bool) ∘ (fun y => Bool.not y) =
      (fun z => Bool.not z) ∘ (id : Bool -> Bool) := by
  exact feedback_completion_naturality
    (fun u _ : Bool => u) (fun u _ : Bool => u) id
    (fun _ _ => rfl) Bool.not

end D5.S3.ObserverMemory.Prediction.FeedbackCompletionNaturality
