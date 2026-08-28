/- GID: D5/S3/ConceptDynamics/Prediction/MacroscopicPredictiveEfficiencyIncrease
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Prediction/MacroscopicPredictiveEfficiencyIncrease
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A persistent fair signal has higher predictive efficiency after noise projection. -/

import D5.S3.ConceptDynamics.Prediction.CoarseGrainingCannotAddInformation
import D5.S3.Entropy.MutualInformationEntropy

/- Library-search audit trail (2026-08-26):
   * Repository searches for macroscopic predictive efficiency, persistent
     uniform bits, and the fixed `1 / 8` transition law found no exact theorem.
   * The body-shape search for `coarseGrainedJoint` found the canonical
     deterministic coarse-law primitive in `CoarseGrainingCannotAddInformation`;
     it is imported and used directly.
   * The repository's `shannonEntropy`, `mutualInformation`, and
     `mutual_information_eq_entropy_sub` are the exact finite-law primitives.
     They use natural logarithms, so division by `Real.log 2` publicly records
     the source's bit units.
   * Pinned Mathlib has `Real.negMulLog`, `Real.log_inv`, and finite Boolean-sum
     simplification, but no finite mutual-information declaration or packaged
     persistent-bit efficiency witness. Loogle and LeanSearch executables were
     unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Prediction.MacroscopicPredictiveEfficiencyIncrease

open D5.S3.ConceptDynamics.Prediction.CoarseGrainingCannotAddInformation
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy

/-- A fair persistent bit paired with independent fresh fair noise has two bits
of microscopic state entropy and one bit of predictive information. Projecting
to the persistent coordinate retains that one bit in one bit of capacity, so
predictive efficiency rises strictly from one half to one while absolute mutual
information stays equal. -/
theorem macroscopic_predictive_efficiency_strictly_increases :
    let microscopicJoint : (Bool × Bool) × (Bool × Bool) -> Real :=
      fun states => if states.1.1 = states.2.1 then 1 / 8 else 0
    let coarse : Bool × Bool -> Bool := Prod.fst
    let macroscopicJoint := coarseGrainedJoint microscopicJoint coarse
    ((forall states, 0 <= microscopicJoint states) /\
      ∑ states, microscopicJoint states = 1) /\
    (forall persistent noiseNow noiseNext,
      microscopicJoint
        ((persistent, noiseNow), (persistent, noiseNext)) = 1 / 8) /\
    (forall persistentNow persistentNext noiseNow noiseNext,
      persistentNow ≠ persistentNext ->
        microscopicJoint
          ((persistentNow, noiseNow), (persistentNext, noiseNext)) = 0) /\
    (forall state, marginal microscopicJoint state = 1 / 4) /\
    (forall state,
      marginal
        (fun states : (Bool × Bool) × (Bool × Bool) =>
          microscopicJoint (states.2, states.1)) state = 1 / 4) /\
    shannonEntropy (marginal microscopicJoint) / Real.log 2 = 2 /\
    mutualInformation microscopicJoint / Real.log 2 = 1 /\
    (mutualInformation microscopicJoint / Real.log 2) /
        (shannonEntropy (marginal microscopicJoint) / Real.log 2) = 1 / 2 /\
    (forall bit, marginal macroscopicJoint bit = 1 / 2) /\
    shannonEntropy (marginal macroscopicJoint) / Real.log 2 = 1 /\
    mutualInformation macroscopicJoint / Real.log 2 = 1 /\
    (mutualInformation macroscopicJoint / Real.log 2) /
        (shannonEntropy (marginal macroscopicJoint) / Real.log 2) = 1 /\
    (mutualInformation microscopicJoint / Real.log 2) /
        (shannonEntropy (marginal microscopicJoint) / Real.log 2) <
    (mutualInformation macroscopicJoint / Real.log 2) /
        (shannonEntropy (marginal macroscopicJoint) / Real.log 2) /\
    mutualInformation macroscopicJoint = mutualInformation microscopicJoint := by
  let microscopicJoint : (Bool × Bool) × (Bool × Bool) -> Real :=
    fun states => if states.1.1 = states.2.1 then 1 / 8 else 0
  let coarse : Bool × Bool -> Bool := Prod.fst
  let macroscopicJoint := coarseGrainedJoint microscopicJoint coarse
  change
    ((forall states, 0 <= microscopicJoint states) /\
      ∑ states, microscopicJoint states = 1) /\
    (forall persistent noiseNow noiseNext,
      microscopicJoint
        ((persistent, noiseNow), (persistent, noiseNext)) = 1 / 8) /\
    (forall persistentNow persistentNext noiseNow noiseNext,
      persistentNow ≠ persistentNext ->
        microscopicJoint
          ((persistentNow, noiseNow), (persistentNext, noiseNext)) = 0) /\
    (forall state, marginal microscopicJoint state = 1 / 4) /\
    (forall state,
      marginal
        (fun states : (Bool × Bool) × (Bool × Bool) =>
          microscopicJoint (states.2, states.1)) state = 1 / 4) /\
    shannonEntropy (marginal microscopicJoint) / Real.log 2 = 2 /\
    mutualInformation microscopicJoint / Real.log 2 = 1 /\
    (mutualInformation microscopicJoint / Real.log 2) /
        (shannonEntropy (marginal microscopicJoint) / Real.log 2) = 1 / 2 /\
    (forall bit, marginal macroscopicJoint bit = 1 / 2) /\
    shannonEntropy (marginal macroscopicJoint) / Real.log 2 = 1 /\
    mutualInformation macroscopicJoint / Real.log 2 = 1 /\
    (mutualInformation macroscopicJoint / Real.log 2) /
        (shannonEntropy (marginal macroscopicJoint) / Real.log 2) = 1 /\
    (mutualInformation microscopicJoint / Real.log 2) /
        (shannonEntropy (marginal microscopicJoint) / Real.log 2) <
      (mutualInformation macroscopicJoint / Real.log 2) /
        (shannonEntropy (marginal macroscopicJoint) / Real.log 2) /\
    mutualInformation macroscopicJoint = mutualInformation microscopicJoint
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoNe : Real.log 2 ≠ 0 := hlogTwoPos.ne'
  have hlogHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  have hlogQuarter : Real.log (1 / 4 : Real) = -2 * Real.log 2 := by
    rw [show (1 / 4 : Real) = ((2 : Real) ^ 2)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  have hlogEighth : Real.log (1 / 8 : Real) = -3 * Real.log 2 := by
    rw [show (1 / 8 : Real) = ((2 : Real) ^ 3)⁻¹ by norm_num,
      Real.log_inv, Real.log_pow]
    norm_num
  have microscopicNonnegative : forall states, 0 <= microscopicJoint states := by
    intro states
    simp only [microscopicJoint]
    split_ifs <;> norm_num
  have microscopicTotal : ∑ states, microscopicJoint states = 1 := by
    norm_num [microscopicJoint, Fintype.sum_prod_type]
  have persistentMass : forall persistent noiseNow noiseNext,
      microscopicJoint
        ((persistent, noiseNow), (persistent, noiseNext)) = 1 / 8 := by
    intros
    simp [microscopicJoint]
  have changedPersistentMass : forall persistentNow persistentNext noiseNow noiseNext,
      persistentNow ≠ persistentNext ->
        microscopicJoint
          ((persistentNow, noiseNow), (persistentNext, noiseNext)) = 0 := by
    intro persistentNow persistentNext noiseNow noiseNext different
    simp [microscopicJoint, different]
  have microscopicFirstMarginal : forall state,
      marginal microscopicJoint state = 1 / 4 := by
    rintro ⟨persistent, noise⟩
    cases persistent <;> cases noise <;>
      norm_num [marginal, microscopicJoint, Fintype.sum_prod_type,
        Fintype.sum_bool]
  have microscopicSecondMarginal : forall state,
      marginal
        (fun states : (Bool × Bool) × (Bool × Bool) =>
          microscopicJoint (states.2, states.1)) state = 1 / 4 := by
    rintro ⟨persistent, noise⟩
    cases persistent <;> cases noise <;>
      norm_num [marginal, microscopicJoint, Fintype.sum_prod_type,
        Fintype.sum_bool]
  have microscopicFirstMarginalFunction :
      marginal microscopicJoint = fun _ => 1 / 4 :=
    funext microscopicFirstMarginal
  have microscopicSecondMarginalFunction :
      marginal
          (fun states : (Bool × Bool) × (Bool × Bool) =>
            microscopicJoint (states.2, states.1)) =
        fun _ => 1 / 4 :=
    funext microscopicSecondMarginal
  have microscopicStateEntropy :
      shannonEntropy (marginal microscopicJoint) = 2 * Real.log 2 := by
    rw [microscopicFirstMarginalFunction]
    norm_num [shannonEntropy, Real.negMulLog, Fintype.sum_prod_type,
      Fintype.sum_bool, hlogQuarter]
    ring
  have microscopicJointEntropy :
      shannonEntropy microscopicJoint = 3 * Real.log 2 := by
    norm_num [shannonEntropy, microscopicJoint, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool, hlogEighth]
    ring
  have microscopicInformation :
      mutualInformation microscopicJoint = Real.log 2 := by
    rw [mutual_information_eq_entropy_sub microscopicJoint microscopicNonnegative,
      microscopicFirstMarginalFunction, microscopicSecondMarginalFunction,
      microscopicJointEntropy]
    norm_num [shannonEntropy, Real.negMulLog, Fintype.sum_prod_type,
      Fintype.sum_bool, hlogQuarter]
    ring
  have macroscopicJointFormula : forall states,
      macroscopicJoint states = if states.1 = states.2 then 1 / 2 else 0 := by
    rintro ⟨first, second⟩
    cases first <;> cases second <;>
      norm_num [macroscopicJoint, coarse, coarseGrainedJoint, microscopicJoint,
        Fintype.sum_prod_type, Fintype.sum_bool]
  have macroscopicFirstMarginal : forall bit,
      marginal macroscopicJoint bit = 1 / 2 := by
    intro bit
    cases bit <;>
      norm_num [marginal, macroscopicJointFormula, Fintype.sum_bool]
  have macroscopicSecondMarginal : forall bit,
      marginal (fun states : Bool × Bool => macroscopicJoint (states.2, states.1)) bit =
        1 / 2 := by
    intro bit
    cases bit <;>
      norm_num [marginal, macroscopicJointFormula, Fintype.sum_bool]
  have macroscopicFirstMarginalFunction :
      marginal macroscopicJoint = fun _ => 1 / 2 :=
    funext macroscopicFirstMarginal
  have macroscopicSecondMarginalFunction :
      marginal (fun states : Bool × Bool => macroscopicJoint (states.2, states.1)) =
        fun _ => 1 / 2 :=
    funext macroscopicSecondMarginal
  have macroscopicStateEntropy :
      shannonEntropy (marginal macroscopicJoint) = Real.log 2 := by
    rw [macroscopicFirstMarginalFunction]
    norm_num [shannonEntropy, Real.negMulLog, Fintype.sum_bool, hlogHalf]
    ring
  have macroscopicJointEntropy :
      shannonEntropy macroscopicJoint = Real.log 2 := by
    norm_num [shannonEntropy, macroscopicJointFormula, Real.negMulLog,
      Fintype.sum_prod_type, Fintype.sum_bool, hlogHalf]
    ring
  have macroscopicNonnegative : forall states, 0 <= macroscopicJoint states := by
    intro states
    rw [macroscopicJointFormula]
    split_ifs <;> norm_num
  have macroscopicInformation :
      mutualInformation macroscopicJoint = Real.log 2 := by
    rw [mutual_information_eq_entropy_sub macroscopicJoint macroscopicNonnegative,
      macroscopicFirstMarginalFunction, macroscopicSecondMarginalFunction,
      macroscopicJointEntropy]
    norm_num [shannonEntropy, Real.negMulLog, Fintype.sum_bool, hlogHalf]
    ring
  have microscopicEntropyBits :
      shannonEntropy (marginal microscopicJoint) / Real.log 2 = 2 := by
    rw [microscopicStateEntropy]
    field_simp [hlogTwoNe]
  have microscopicInformationBits :
      mutualInformation microscopicJoint / Real.log 2 = 1 := by
    rw [microscopicInformation]
    field_simp [hlogTwoNe]
  have macroscopicEntropyBits :
      shannonEntropy (marginal macroscopicJoint) / Real.log 2 = 1 := by
    rw [macroscopicStateEntropy]
    field_simp [hlogTwoNe]
  have macroscopicInformationBits :
      mutualInformation macroscopicJoint / Real.log 2 = 1 := by
    rw [macroscopicInformation]
    field_simp [hlogTwoNe]
  refine ⟨⟨microscopicNonnegative, microscopicTotal⟩, persistentMass,
    changedPersistentMass, microscopicFirstMarginal, microscopicSecondMarginal,
    microscopicEntropyBits, microscopicInformationBits, ?_,
    macroscopicFirstMarginal, macroscopicEntropyBits, macroscopicInformationBits,
    ?_, ?_, ?_⟩
  · rw [microscopicInformationBits, microscopicEntropyBits]
  · rw [macroscopicInformationBits, macroscopicEntropyBits]
    norm_num
  · rw [microscopicInformationBits, microscopicEntropyBits,
      macroscopicInformationBits, macroscopicEntropyBits]
    norm_num
  · rw [macroscopicInformation, microscopicInformation]

#print axioms macroscopic_predictive_efficiency_strictly_increases

end D5.S3.ConceptDynamics.Prediction.MacroscopicPredictiveEfficiencyIncrease
