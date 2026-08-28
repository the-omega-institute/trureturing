/- GID: D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact rollback from a joint update-log record is equivalent to injectivity. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Logic.Function.Basic

/-! Library-search audit trail (2026-08-29):
* `rg -n "rollback|injective|left.*inverse|conceptJoin" D5/S3/ConceptDynamics -g '*.lean'`
  found related recovery results and the canonical paired readout `conceptJoin`, but no frozen
  theorem stating this exact rollback criterion.
* `rg -n "injective_iff_hasLeftInverse" .lake/packages/mathlib/Mathlib -g '*.lean'`
  found the exact pinned equivalence `Function.injective_iff_hasLeftInverse`; the proof applies
  it directly.
* Body-shape searches for `fun x => (U x, L x)` and equivalent pair-readout forms found
  `ConceptJoinUniversal.conceptJoin`, which is imported rather than redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reversibility.ExactRollbackInjectivityCriterion

open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- An exact rollback map exists for the joint update-log record exactly when that record is
injective. -/
theorem exact_rollback_iff_joint_record_injective
    {X Y M : Type*} [Nonempty X] (U : X → Y) (L : X → M) :
    (∃ R : Y × M → X, ∀ x, R (conceptJoin U L x) = x) ↔
      Function.Injective (conceptJoin U L) := by
  change Function.HasLeftInverse (conceptJoin U L) ↔
    Function.Injective (conceptJoin U L)
  exact (Function.injective_iff_hasLeftInverse (f := conceptJoin U L)).symm

example :
    (∃ R : Bool × Unit → Bool,
      ∀ x, R (conceptJoin (fun x : Bool => x) (fun _ => ()) x) = x) := by
  exact ⟨Prod.fst, fun _ => rfl⟩

#print axioms exact_rollback_iff_joint_record_injective

end D5.S3.ConceptDynamics.Reversibility.ExactRollbackInjectivityCriterion
