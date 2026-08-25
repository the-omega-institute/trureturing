/- GID: D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The joint-target kernel quotient is minimal among sufficient readouts. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * The exact current-tree primitive `jointReadout` constructs the source's
     dependent joint target and is imported rather than redeclared.
   * `MultiTargetMinimalSufficiency` proves the adjacent joint-readout universal
     property but does not publicly expose the canonical kernel quotient or its
     projection. `GlobalProfileQuotientUniversality` adds a nonempty-state
     premise absent from the source, so neither is an exact theorem hit.
   * Pinned Mathlib supplies `Quotient.lift`, `Quotient.inductionOn`, and
     `Quotient.sound`; no theorem packages the full dependent-family statement.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SufficiencyQuotient.TargetFamilyMinimalQuotient

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- The canonical quotient by simultaneous target agreement recovers every
target uniquely. Any readout recovering all targets has a finer kernel and
therefore refines the canonical quotient projection. -/
theorem target_family_minimal_quotient
    {I : Type u} {X : Type v} {Y : I -> Type w} {O : Type z}
    (targets : forall index, X -> Y index) (readout : X -> O)
    (sufficient : forall index,
      exists factor : O -> Y index, targets index = factor ∘ readout) :
    let profile := jointReadout targets
    let projection : X -> Quotient (Setoid.ker profile) :=
      fun state => Quotient.mk (Setoid.ker profile) state
    (forall index,
      ∃! descend : Quotient (Setoid.ker profile) -> Y index,
        targets index = descend ∘ projection) /\
      Setoid.ker readout <= Setoid.ker profile /\
      Setoid.ker readout <= Setoid.ker projection := by
  dsimp only
  let profile := jointReadout targets
  let projection : X -> Quotient (Setoid.ker profile) :=
    fun state => Quotient.mk (Setoid.ker profile) state
  have targetDescent : forall index,
      ∃! descend : Quotient (Setoid.ker profile) -> Y index,
        targets index = descend ∘ projection := by
    intro index
    let descend : Quotient (Setoid.ker profile) -> Y index :=
      Quotient.lift (targets index) (by
        intro left right sameProfile
        exact congrFun sameProfile index)
    have factorization : targets index = descend ∘ projection := by
      funext state
      rfl
    refine ⟨descend, factorization, ?_⟩
    intro candidate candidateFactorization
    funext quotientState
    induction quotientState using Quotient.inductionOn with
    | _ state =>
        have candidateValue := congrFun candidateFactorization state
        have descendValue := congrFun factorization state
        exact candidateValue.symm.trans descendValue
  have kernelInclusion : Setoid.ker readout <= Setoid.ker profile := by
    intro left right sameReadout
    change profile left = profile right
    funext index
    obtain ⟨factor, factorization⟩ := sufficient index
    change targets index left = targets index right
    rw [factorization]
    exact congrArg factor sameReadout
  refine ⟨targetDescent, kernelInclusion, ?_⟩
  intro left right sameReadout
  exact Quotient.sound (kernelInclusion sameReadout)

#print axioms target_family_minimal_quotient

end D5.S3.ConceptDynamics.SufficiencyQuotient.TargetFamilyMinimalQuotient
