/- GID: D5/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/ConditionalInformationSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero conditional information characterizes independence and support sufficiency. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-09-05):
   * Repository searches found the exact conditional-product characterization
     `conditional_mutual_information_eq_zero_iff_conditional_product`, which is
     applied directly for the first conjunct and the forward support argument.
   * The related positive-prior completion theorem requires positive mass at
     every state, so it does not cover the present positive-support statement.
   * Pinned Mathlib has conditional-independence and KL-divergence APIs but no
     exact finite-real conditional-information theorem on this carrier.
   * External searches found entropy developments but no applicable exact hit.
   * Body-shape searches found no canonical support-restricted sufficiency
     primitive or prior-kernel-concept joint law, so both remain inline. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.ConditionalInformationSufficiency

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Submodularity.ConditionalMutualInformation
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped Classical in
/-- In a finite channel model, zero conditional mutual information is both
conditional independence and constancy of the target kernel on every
positive-prior concept fiber. -/
theorem conditional_information_zero_iff_support_sufficiency
    {X C Y : Type*} [Fintype X] [Fintype C] [Fintype Y]
    (prior : PMF X) (kernel : X -> PMF Y) (concept : X -> C) :
    let jointLaw : X × (C × Y) -> Real := fun q =>
      if q.2.1 = concept q.1 then
        (prior q.1).toReal * (kernel q.1 q.2.2).toReal
      else 0
    let conditionedLaw : C × (X × Y) -> Real := yFirstLaw jointLaw
    (conditionalMutualInformation conditionedLaw = 0 <->
      forall c, marginal conditionedLaw c ≠ 0 ->
        conditional conditionedLaw c = fun q : X × Y =>
          marginal (conditional conditionedLaw c) q.1 *
            marginal
              (fun r : Y × X => conditional conditionedLaw c (r.2, r.1)) q.2) /\
    (conditionalMutualInformation conditionedLaw = 0 <->
      forall x x', 0 < (prior x).toReal -> 0 < (prior x').toReal ->
        concept x = concept x' -> kernel x = kernel x') := by
  classical
  let jointLaw : X × (C × Y) -> Real := fun q =>
    if q.2.1 = concept q.1 then
      (prior q.1).toReal * (kernel q.1 q.2.2).toReal
    else 0
  let conditionedLaw : C × (X × Y) -> Real := yFirstLaw jointLaw
  change
    (conditionalMutualInformation conditionedLaw = 0 <->
      forall c, marginal conditionedLaw c ≠ 0 ->
        conditional conditionedLaw c = fun q : X × Y =>
          marginal (conditional conditionedLaw c) q.1 *
            marginal
              (fun r : Y × X => conditional conditionedLaw c (r.2, r.1)) q.2) /\
    (conditionalMutualInformation conditionedLaw = 0 <->
      forall x x', 0 < (prior x).toReal -> 0 < (prior x').toReal ->
        concept x = concept x' -> kernel x = kernel x')
  have kernelSum : forall x, ∑ y : Y, (kernel x y).toReal = 1 := by
    intro x
    have hsum : (∑ y : Y, kernel x y) = 1 := by
      simpa using (kernel x).tsum_coe
    calc
      (∑ y : Y, (kernel x y).toReal) = (∑ y : Y, kernel x y).toReal := by
        symm
        exact ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top (kernel x) y)
      _ = 1 := by rw [hsum]; simp
  have priorSum : ∑ x : X, (prior x).toReal = 1 := by
    have hsum : (∑ x : X, prior x) = 1 := by
      simpa using prior.tsum_coe
    calc
      (∑ x : X, (prior x).toReal) = (∑ x : X, prior x).toReal := by
        symm
        exact ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top prior x)
      _ = 1 := by rw [hsum]; simp
  have jointNonneg : forall q, 0 <= jointLaw q := by
    intro q
    simp only [jointLaw]
    split <;> positivity
  have jointSum : ∑ q, jointLaw q = 1 := by
    calc
      (∑ q, jointLaw q) =
          ∑ x : X, ∑ c : C,
            if c = concept x then (prior x).toReal else 0 := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : c = concept x
        · simp [jointLaw, hc, ← Finset.mul_sum, kernelSum x]
        · simp [jointLaw, hc]
      _ = ∑ x : X, (prior x).toReal := by simp
      _ = 1 := priorSum
  have conditionedNonneg : forall q, 0 <= conditionedLaw q := fun q => jointNonneg _
  have conditionedSum : ∑ q, conditionedLaw q = 1 := by
    rw [← jointSum]
    simp only [conditionedLaw, yFirstLaw, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have conditionedIsLaw :
      (forall q, 0 <= conditionedLaw q) /\ ∑ q, conditionedLaw q = 1 :=
    ⟨conditionedNonneg, conditionedSum⟩
  constructor
  · exact conditional_mutual_information_eq_zero_iff_conditional_product
      conditionedLaw conditionedIsLaw
  · constructor
    · intro informationZero
      have slices :=
        (conditional_mutual_information_eq_zero_iff_conditional_product
          conditionedLaw conditionedIsLaw).1 informationZero
      let fiberMass : C -> Real := fun c =>
        ∑ z : X, if c = concept z then (prior z).toReal else 0
      let targetMass : C -> Y -> Real := fun c value =>
        ∑ z : X,
          if c = concept z then
            (prior z).toReal * (kernel z value).toReal
          else 0
      have conditionedMarginal : forall c,
          marginal conditionedLaw c = fiberMass c := by
        intro c
        simp only [marginal, conditionedLaw, yFirstLaw, jointLaw, fiberMass,
          Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : c = concept z
        · simp [hz, ← Finset.mul_sum, kernelSum z]
        · simp [hz]
      have conditionalFirst : forall c x,
          marginal (conditional conditionedLaw c) x =
            if c = concept x then (prior x).toReal / fiberMass c else 0 := by
        intro c x
        rw [marginal]
        simp only [conditional, ← Finset.sum_div]
        change
          (∑ y, conditionedLaw (c, (x, y))) / marginal conditionedLaw c = _
        rw [conditionedMarginal]
        simp only [conditionedLaw, yFirstLaw, jointLaw]
        by_cases hx : c = concept x
        · simp [hx, ← Finset.mul_sum, kernelSum x]
        · simp [hx]
      have conditionalSecond : forall c y,
          marginal
              (fun r : Y × X => conditional conditionedLaw c (r.2, r.1)) y =
            targetMass c y / fiberMass c := by
        intro c y
        rw [marginal]
        simp only [conditional, ← Finset.sum_div]
        change
          (∑ x, conditionedLaw (c, (x, y))) / marginal conditionedLaw c = _
        rw [conditionedMarginal]
        simp [conditionedLaw, yFirstLaw, jointLaw, targetMass]
      intro x x' hx hx' sameConcept
      apply PMF.ext
      intro y
      rw [← ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top (kernel x) y) (PMF.apply_ne_top (kernel x') y)]
      have fiberMassPositive : 0 < fiberMass (concept x) := by
        apply Finset.sum_pos'
        · intro z _
          by_cases hz : concept x = concept z
          · simp [hz, ENNReal.toReal_nonneg]
          · simp [hz]
        · exact ⟨x, Finset.mem_univ x, by simp [hx]⟩
      have marginalNonzero : marginal conditionedLaw (concept x) ≠ 0 := by
        rw [conditionedMarginal]
        exact fiberMassPositive.ne'
      have atX := congrFun (slices (concept x) marginalNonzero) (x, y)
      have atX' := congrFun (slices (concept x) marginalNonzero) (x', y)
      rw [conditionalFirst, conditionalSecond] at atX atX'
      simp only [conditional] at atX atX'
      rw [conditionedMarginal] at atX atX'
      simp only [conditionedLaw, yFirstLaw, jointLaw, if_pos] at atX
      simp only [conditionedLaw, yFirstLaw, jointLaw, sameConcept, if_pos] at atX'
      rw [← sameConcept] at atX'
      have atXReduced :
          (kernel x y).toReal * fiberMass (concept x) =
            targetMass (concept x) y := by
        field_simp [hx.ne', fiberMassPositive.ne'] at atX
        nlinarith
      have atX'Reduced :
          (kernel x' y).toReal * fiberMass (concept x) =
            targetMass (concept x) y := by
        field_simp [hx'.ne', fiberMassPositive.ne'] at atX'
        nlinarith
      exact mul_right_cancel₀ fiberMassPositive.ne'
        (atXReduced.trans atX'Reduced.symm)
    · intro supportSufficient
      let defaultState : X := prior.support_nonempty.some
      let representative : C -> X := fun c =>
        if h : exists x, 0 < (prior x).toReal /\ concept x = c then
          Classical.choose h
        else defaultState
      let channel : C -> Y -> Real := fun c y =>
        (kernel (representative c) y).toReal
      have channelSum : forall c, ∑ y, channel c y = 1 := by
        intro c
        exact kernelSum (representative c)
      let stateConceptLaw : X × C -> Real := fun q =>
        if q.2 = concept q.1 then (prior q.1).toReal else 0
      have jointFormula : jointLaw = fun q : X × (C × Y) =>
          stateConceptLaw (q.1, q.2.1) * channel q.2.1 q.2.2 := by
        funext q
        by_cases hc : q.2.1 = concept q.1
        · by_cases hp : 0 < (prior q.1).toReal
          · have hexists : exists x,
                0 < (prior x).toReal /\ concept x = q.2.1 :=
              ⟨q.1, hp, hc.symm⟩
            have hrepresentativePositive :
                0 < (prior (representative q.2.1)).toReal := by
              simp only [representative, dif_pos hexists]
              exact (Classical.choose_spec hexists).1
            have hrepresentativeConcept :
                concept (representative q.2.1) = q.2.1 := by
              simp only [representative, dif_pos hexists]
              exact (Classical.choose_spec hexists).2
            have hkernel := supportSufficient q.1 (representative q.2.1)
              hp hrepresentativePositive
              (hc.symm.trans hrepresentativeConcept.symm)
            simp [jointLaw, stateConceptLaw, channel, hc, hkernel]
          · have hpzero : (prior q.1).toReal = 0 :=
              le_antisymm (le_of_not_gt hp) ENNReal.toReal_nonneg
            simp [jointLaw, stateConceptLaw, hc, hpzero]
        · simp [jointLaw, stateConceptLaw, hc]
      have markov : forall x c y,
          jointLaw (x, (c, y)) * marginal (yFirstLaw jointLaw) c =
            xyProjection jointLaw (x, c) *
              xzProjection (yFirstLaw jointLaw) (c, y) := by
        rw [jointFormula]
        exact markov_of_channel stateConceptLaw channel channelSum
      exact conditional_mutual_information_eq_zero_of_markov
        jointLaw ⟨jointNonneg, jointSum⟩ markov

#print axioms conditional_information_zero_iff_support_sufficiency

end D5.S3.ConceptDynamics.Completion.ConditionalInformationSufficiency
