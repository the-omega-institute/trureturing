/- GID: D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/TranslationLossMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic postprocessing enlarges target defects and target residual entropy. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import D5.S3.Entropy.Forgetting.CapacityMonotone
import D5.S3.Entropy.MutualInformationSymm
import D5.S3.Entropy.Submodularity.MarkovDataProcessing

/- Library-search audit trail (2026-08-23):
   * Exact family hits `Concept` and `defectRelation` construct the translation
     maps and target-sensitive loss sets; both are imported rather than redeclared.
   * Exact repository hit `mutual_information_le_of_markov` supplies the finite
     data-processing inequality and is applied directly to the deterministic
     channel induced by the postprocessor.
   * Exact repository hits `entropy_chain_rule`,
     `mutual_information_eq_entropy_sub`, and `mutual_information_symm` identify
     the resulting information inequality with the source's conditional-target
     entropy inequality and are applied directly.
   * `refinement_information_residual_monotone` concerns source-state entropy
     given a readout, not target entropy. `coarse_graining_cannot_add_information`
     processes both coordinates of a joint state law. Repository and pinned-
     Mathlib searches found no exact target-conditioned postprocessing theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Entropy.MutualInformationSymm
open D5.S3.Entropy.Submodularity.StrongSubadditivity
open D5.S3.Entropy.Submodularity.MarkovDataProcessing

/-- The joint law of a finite readout and target, constructed by pushing the
state law through their paired observation map. -/
noncomputable def readoutTargetLaw
    {X Readout Target : Type*} [Fintype X]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target) : Readout × Target → Real :=
  pushforward (fun x => (readout x, target x)) mass

/-- Conditional target entropy remaining after observing a finite readout. -/
noncomputable def targetResidualEntropy
    {X Readout Target : Type*} [Fintype X] [Fintype Readout] [Fintype Target]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target) : Real :=
  conditionalEntropy (readoutTargetLaw mass readout target)

private noncomputable def translationExtension
    {X Fine Coarse Target : Type*} [Fintype X]
    (mass : X → Real) (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target) : Target × (Fine × Coarse) → Real :=
  by
    classical
    exact fun q => readoutTargetLaw mass fine target (q.2.1, q.1) *
      if postprocess q.2.1 = q.2.2 then 1 else 0

private theorem readoutTargetLaw_is_law
    {X Readout Target : Type*}
    [Fintype X] [Fintype Readout] [Fintype Target]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target)
    (hmass : (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1) :
    (∀ q, 0 ≤ readoutTargetLaw mass readout target q) ∧
      ∑ q, readoutTargetLaw mass readout target q = 1 := by
  classical
  constructor
  · intro q
    simp only [readoutTargetLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact hmass.1 x
      · exact le_rfl
  · simp only [readoutTargetLaw, pushforward]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x, mass x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_eq_single (readout x, target x)]
        · simp
        · intro q _ different
          simp [Ne.symm different]
        · simp
      _ = 1 := hmass.2

private theorem translationExtension_is_law
    {X Fine Coarse Target : Type*}
    [Fintype X] [Fintype Fine] [Fintype Coarse] [Fintype Target]
    (mass : X → Real) (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target)
    (hmass : (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1) :
    (∀ q, 0 ≤ translationExtension mass fine postprocess target q) ∧
      ∑ q, translationExtension mass fine postprocess target q = 1 := by
  classical
  have fineLaw := readoutTargetLaw_is_law mass fine target hmass
  constructor
  · intro q
    apply mul_nonneg (fineLaw.1 _)
    split_ifs <;> norm_num
  · simp only [translationExtension, Fintype.sum_prod_type]
    calc
      (∑ targetValue, ∑ fineValue, ∑ coarseValue,
          readoutTargetLaw mass fine target (fineValue, targetValue) *
            if postprocess fineValue = coarseValue then 1 else 0) =
          ∑ targetValue, ∑ fineValue,
            readoutTargetLaw mass fine target (fineValue, targetValue) := by
        apply Finset.sum_congr rfl
        intro targetValue _
        apply Finset.sum_congr rfl
        intro fineValue _
        simp
      _ = ∑ q, readoutTargetLaw mass fine target q := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = 1 := fineLaw.2

private theorem xyProjection_translationExtension
    {X Fine Coarse Target : Type*}
    [Fintype X] [Fintype Coarse]
    (mass : X → Real) (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target) :
    xyProjection (translationExtension mass fine postprocess target) =
      fun q : Target × Fine => readoutTargetLaw mass fine target (q.2, q.1) := by
  classical
  funext q
  simp [xyProjection, translationExtension]

private theorem xzProjection_translationExtension
    {X Fine Coarse Target : Type*}
    [Fintype X] [Fintype Fine]
    (mass : X → Real) (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target) :
    xzProjection (translationExtension mass fine postprocess target) =
      fun q : Target × Coarse =>
        readoutTargetLaw mass (postprocess ∘ fine) target (q.2, q.1) := by
  classical
  funext q
  simp only [xzProjection, translationExtension, readoutTargetLaw, pushforward]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (fine x)]
  · unfold Function.comp
    by_cases hpost : postprocess (fine x) = q.2
    · by_cases htarget : target x = q.1
      · have hleft : (fine x, target x) = (fine x, q.1) :=
          Prod.ext rfl htarget
        have hright : (postprocess (fine x), target x) = (q.2, q.1) :=
          Prod.ext hpost htarget
        rw [if_pos hleft, if_pos hright, if_pos hpost, mul_one]
      · have hleft : (fine x, target x) ≠ (fine x, q.1) := by
          intro hpair
          exact htarget (congrArg Prod.snd hpair)
        have hright : (postprocess (fine x), target x) ≠ (q.2, q.1) := by
          intro hpair
          exact htarget (congrArg Prod.snd hpair)
        rw [if_neg hleft, if_neg hright, if_pos hpost, zero_mul]
    · have hright : (postprocess (fine x), target x) ≠ (q.2, q.1) := by
        intro hpair
        exact hpost (congrArg Prod.fst hpair)
      rw [if_neg hright, if_neg hpost, mul_zero]
  · intro fineValue _ different
    simp [Prod.ext_iff, Ne.symm different]
  · simp

private theorem translationExtension_is_markov
    {X Fine Coarse Target : Type*}
    [Fintype X] [Fintype Coarse] [Fintype Target]
    (mass : X → Real) (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target) :
    ∀ targetValue fineValue coarseValue,
      translationExtension mass fine postprocess target
          (targetValue, (fineValue, coarseValue)) *
        marginal (yFirstLaw
          (translationExtension mass fine postprocess target)) fineValue =
      xyProjection (translationExtension mass fine postprocess target)
          (targetValue, fineValue) *
        xzProjection (yFirstLaw
          (translationExtension mass fine postprocess target))
          (fineValue, coarseValue) := by
  classical
  have channelSum : ∀ fineValue,
      ∑ coarseValue, (if postprocess fineValue = coarseValue then (1 : Real) else 0) = 1 :=
    fun fineValue => by simp
  unfold translationExtension
  exact markov_of_channel
    (fun pair : Target × Fine =>
      readoutTargetLaw mass fine target (pair.2, pair.1))
    (fun fineValue coarseValue =>
      if postprocess fineValue = coarseValue then (1 : Real) else 0)
    channelSum

private theorem targetMarginal_readoutTargetLaw
    {X Readout Target : Type*}
    [Fintype X] [Fintype Readout]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target) :
    marginal (fun q : Target × Readout =>
      readoutTargetLaw mass readout target (q.2, q.1)) =
        pushforward target mass := by
  classical
  funext targetValue
  simp only [marginal, readoutTargetLaw, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (readout x)]
  · simp [Prod.ext_iff]
  · intro readoutValue _ different
    simp [Prod.ext_iff, Ne.symm different]
  · simp

private theorem targetResidualEntropy_eq_entropy_sub_information
    {X Readout Target : Type*}
    [Fintype X] [Fintype Readout] [Fintype Target]
    (mass : X → Real) (readout : Concept X Readout)
    (target : Concept X Target) (hmass : ∀ x, 0 ≤ mass x) :
    targetResidualEntropy mass readout target =
      shannonEntropy (pushforward target mass) -
        mutualInformation (readoutTargetLaw mass readout target) := by
  have lawNonnegative : ∀ q, 0 ≤ readoutTargetLaw mass readout target q := by
    intro q
    classical
    simp only [readoutTargetLaw, pushforward]
    exact Finset.sum_nonneg fun x _ => by
      split_ifs
      · exact hmass x
      · exact le_rfl
  have chain := entropy_chain_rule
    (readoutTargetLaw mass readout target) lawNonnegative
  have information := mutual_information_eq_entropy_sub
    (readoutTargetLaw mass readout target) lawNonnegative
  rw [targetMarginal_readoutTargetLaw mass readout target] at information
  unfold targetResidualEntropy
  linarith

/-- Deterministic postprocessing preserves every earlier target defect and,
for every finite probability law, cannot decrease the target entropy left
unresolved by the readout. -/
theorem translation_loss_monotone
    {X Fine Coarse Target : Type*}
    [Fintype X] [Fintype Fine] [Fintype Coarse] [Fintype Target]
    (mass : X → Real) (hmass : (∀ x, 0 ≤ mass x) ∧ ∑ x, mass x = 1)
    (fine : Concept X Fine) (postprocess : Fine → Coarse)
    (target : Concept X Target) :
    defectRelation fine target ⊆
        defectRelation (postprocess ∘ fine) target ∧
      targetResidualEntropy mass fine target ≤
        targetResidualEntropy mass (postprocess ∘ fine) target := by
  constructor
  · rintro pair ⟨sameFine, differentTarget⟩
    exact ⟨congrArg postprocess sameFine, differentTarget⟩
  · have dataProcessing := mutual_information_le_of_markov
      (translationExtension mass fine postprocess target)
      (translationExtension_is_law mass fine postprocess target hmass)
      (translationExtension_is_markov mass fine postprocess target)
    rw [xyProjection_translationExtension,
      xzProjection_translationExtension] at dataProcessing
    have informationMonotone :
        mutualInformation
            (readoutTargetLaw mass (postprocess ∘ fine) target) ≤
          mutualInformation (readoutTargetLaw mass fine target) := by
      rw [← mutual_information_symm
        (readoutTargetLaw mass (postprocess ∘ fine) target),
        ← mutual_information_symm (readoutTargetLaw mass fine target)]
      exact dataProcessing
    rw [targetResidualEntropy_eq_entropy_sub_information
        mass fine target hmass.1,
      targetResidualEntropy_eq_entropy_sub_information
        mass (postprocess ∘ fine) target hmass.1]
    linarith

/-- A constant postprocessor preserves an explicit target defect. -/
example :
    defectRelation (id : Concept Bool Bool) (id : Concept Bool Bool) ⊆
      defectRelation ((fun _ : Bool => ()) ∘ (id : Concept Bool Bool))
        (id : Concept Bool Bool) :=
  (translation_loss_monotone (fun _ : Bool => (1 / 2 : Real))
    ⟨fun _ => by norm_num, by norm_num [Fintype.sum_bool]⟩
    (id : Concept Bool Bool) (fun _ : Bool => ())
    (id : Concept Bool Bool)).1

#print axioms readoutTargetLaw
#print axioms targetResidualEntropy
#print axioms translation_loss_monotone

end D5.S3.ConceptDynamics.Communication.TranslationLossMonotonicity
