/- GID: D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite defect snapshots are covered exactly when no chosen-package pair stays blind. -/

import D5.S3.ConceptDynamics.ResidualCoverage.WeightedResidualCoverage
import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction

/- Library-search audit trail (2026-08-24):
   * `rg -n 'separatesPair|coveredBy_iff_not_mem_jointKernel|
     exactCover_iff_no_blind_pair' D5 --glob '*.lean'` found no repository hit.
   * Pinned Mathlib searches for `decide_eq_true_eq`, `Set.mem_iInter`,
     `Finset.single_le_sum`, and `not_congr` found only the generic tools used
     below, not this adapter between Boolean coverage and concept kernels.
   * The uncovered-weight equivalence requires positive weight on every
     snapshot member. Without this correction, an uncovered zero-weight blind
     pair makes the left side zero while falsifying the right side. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ResidualCoverage.ResidualSeparationAdapter

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.ResidualCoverage.WeightedResidualCoverage

/-- A concept separates a pair exactly when its two readout values differ. -/
def separatesPair {X Output : Type*} [DecidableEq Output]
    (definition : Concept X Output) (pair : X × X) : Bool :=
  decide
    ((definition : X → Output) pair.1 ≠
      (definition : X → Output) pair.2)

/-- Boolean pair separation reflects readout inequality. -/
theorem separatesPair_eq_true_iff
    {X Output : Type*} [DecidableEq Output]
    (definition : Concept X Output) (pair : X × X) :
    separatesPair definition pair = true ↔
      (definition : X → Output) pair.1 ≠
        (definition : X → Output) pair.2 := by
  simp [separatesPair]

/-- Boolean coverage by a finite package is nonmembership in its joint kernel. -/
theorem coveredBy_iff_not_mem_jointKernel
    {X Output : Type*} [DecidableEq Output]
    [DecidableEq (Concept X Output)]
    (chosen : Finset (Concept X Output)) (pair : X × X) :
    CoveredBy separatesPair chosen pair = true ↔
      pair ∉ jointKernel
        (fun definition : (chosen : Set (Concept X Output)) =>
          (definition.1 : X → Output)) := by
  rw [coveredBy_eq_true_iff]
  constructor
  · rintro ⟨definition, inChosen, separated⟩ inKernel
    unfold jointKernel at inKernel
    have kernelMember :=
      Set.mem_iInter.1 inKernel
        (⟨definition, inChosen⟩ : (chosen : Set (Concept X Output)))
    unfold conceptKernel at kernelMember
    exact (separatesPair_eq_true_iff definition pair).1 separated kernelMember
  · intro notInKernel
    by_contra noWitness
    apply notInKernel
    unfold jointKernel
    apply Set.mem_iInter.2
    intro definition
    unfold conceptKernel
    by_contra separated
    apply noWitness
    exact ⟨definition.1, definition.2,
      (separatesPair_eq_true_iff definition.1 pair).2 separated⟩

/-- A defect snapshot is exactly covered iff no listed pair remains blind. -/
theorem exactCover_iff_no_blind_pair
    {X C Target Output : Type*} [DecidableEq Output]
    [DecidableEq (Concept X Output)]
    (residuals : Finset (X × X)) (q : Concept X C)
    (target : Concept X Target)
    (snapshot : ∀ pair ∈ residuals, pair ∈ defectRelation q target)
    (chosen : Finset (Concept X Output)) :
    ExactCover residuals separatesPair chosen ↔
      ∀ pair ∈ residuals,
        pair ∉ blindResidual (chosen : Set (Concept X Output)) q target := by
  constructor
  · intro exact pair inResiduals inBlindResidual
    have notInKernel :=
      (coveredBy_iff_not_mem_jointKernel chosen pair).1
        (exact pair inResiduals)
    exact notInKernel inBlindResidual.2
  · intro noBlindPair pair inResiduals
    apply (coveredBy_iff_not_mem_jointKernel chosen pair).2
    intro inKernel
    apply noBlindPair pair inResiduals
    exact ⟨snapshot pair inResiduals, inKernel⟩

/-- With positive snapshot weights, zero uncovered mass is equivalent to exact cover. -/
theorem uncoveredWeight_eq_zero_iff_exactCover_of_pos
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition)
    (positive : ∀ residual ∈ residuals, 0 < weight residual) :
    UncoveredWeight residuals weight separates chosen = 0 ↔
      ExactCover residuals separates chosen := by
  constructor
  · intro zeroWeight residual inResiduals
    cases covered : CoveredBy separates chosen residual with
    | true => rfl
    | false =>
        have residualWeightBound :
            weight residual ≤
              UncoveredWeight residuals weight separates chosen := by
          unfold UncoveredWeight
          have singleBound :=
            Finset.single_le_sum
              (f := fun candidate =>
                if CoveredBy separates chosen candidate then
                  0
                else weight candidate)
              (fun candidate _ => Nat.zero_le _) inResiduals
          simpa [covered] using singleBound
        rw [zeroWeight] at residualWeightBound
        exact False.elim
          ((Nat.not_lt_of_ge residualWeightBound) (positive residual inResiduals))
  · intro exact
    exact exactCover_uncoveredWeight_eq_zero
      residuals weight separates chosen exact

/-- Positive snapshot weights make zero uncovered mass equivalent to no blind pair. -/
theorem uncoveredWeight_zero_iff_no_blind_pair
    {X C Target Output : Type*} [DecidableEq Output]
    [DecidableEq (Concept X Output)]
    (residuals : Finset (X × X)) (weight : X × X → Nat)
    (q : Concept X C) (target : Concept X Target)
    (snapshot : ∀ pair ∈ residuals, pair ∈ defectRelation q target)
    (positive : ∀ pair ∈ residuals, 0 < weight pair)
    (chosen : Finset (Concept X Output)) :
    UncoveredWeight residuals weight separatesPair chosen = 0 ↔
      ∀ pair ∈ residuals,
        pair ∉ blindResidual (chosen : Set (Concept X Output)) q target := by
  rw [uncoveredWeight_eq_zero_iff_exactCover_of_pos
    residuals weight separatesPair chosen positive]
  exact exactCover_iff_no_blind_pair residuals q target snapshot chosen

#print axioms separatesPair_eq_true_iff
#print axioms coveredBy_iff_not_mem_jointKernel
#print axioms exactCover_iff_no_blind_pair
#print axioms uncoveredWeight_eq_zero_iff_exactCover_of_pos
#print axioms uncoveredWeight_zero_iff_no_blind_pair

end D5.S3.ConceptDynamics.ResidualCoverage.ResidualSeparationAdapter
