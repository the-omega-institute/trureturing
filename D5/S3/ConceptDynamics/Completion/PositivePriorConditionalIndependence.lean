/- GID: D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive finite priors identify stochastic sufficiency with conditional independence. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-26):
   * Current-tree searches for finite positive-support conditional independence,
     stochastic sufficiency, conditional-law factorization, and kernel descent
     found no exact D5 theorem stating both directions on the source carrier.
   * Exact D5 hit `markov_of_channel` proves the forward conditional-product
     identity for a channel-generated joint law and is applied directly.
   * Exact pinned-Mathlib hits `PMF`, `PMF.tsum_coe`, `PMF.apply_ne_top`,
     `ENNReal.toReal_sum`, and `Function.factorsThrough_iff` supply the finite
     probability carrier, normalization bridge, and whole-codomain factor.
   * Body-shape searches for a joint law built from a prior, deterministic
     concept, and stochastic kernel found no canonical D5 primitive. The law is
     therefore constructed inline in the public statement, with no new def. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.PositivePriorConditionalIndependence

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped Classical in
/-- For a finite state space with pointwise positive prior mass, a stochastic
target kernel factors through a deterministic concept exactly when the joint
law constructed from that prior, concept, and kernel makes the target and
state conditionally independent given the concept. -/
theorem positive_prior_sufficiency_iff_conditional_independence
    {X C Y : Type*} [Fintype X] [Fintype Y]
    (prior : PMF X) (kernel : X -> PMF Y) (concept : X -> C)
    (priorPositive : forall x, 0 < (prior x).toReal) :
    let jointLaw : X × (C × Y) -> Real := fun q =>
      if q.2.1 = concept q.1 then
        (prior q.1).toReal * (kernel q.1 q.2.2).toReal
      else 0
    (exists reducedKernel : C -> PMF Y,
      kernel = reducedKernel ∘ concept) <->
      forall x c y,
        jointLaw (x, (c, y)) * marginal (yFirstLaw jointLaw) c =
          xyProjection jointLaw (x, c) *
            xzProjection (yFirstLaw jointLaw) (c, y) := by
  classical
  dsimp only
  have kernelSum : forall x, ∑ y : Y, (kernel x y).toReal = 1 := by
    intro x
    have hsum : (∑ y : Y, kernel x y) = 1 := by
      simpa using (kernel x).tsum_coe
    calc
      (∑ y : Y, (kernel x y).toReal) = (∑ y : Y, kernel x y).toReal := by
        symm
        exact ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top (kernel x) y)
      _ = 1 := by rw [hsum]; simp
  constructor
  · rintro ⟨reducedKernel, factorization⟩
    have reducedSum : forall c, ∑ y : Y, (reducedKernel c y).toReal = 1 := by
      intro c
      have hsum : (∑ y : Y, reducedKernel c y) = 1 := by
        simpa using (reducedKernel c).tsum_coe
      calc
        (∑ y : Y, (reducedKernel c y).toReal) =
            (∑ y : Y, reducedKernel c y).toReal := by
          symm
          exact ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top (reducedKernel c) y)
        _ = 1 := by rw [hsum]; simp
    let stateConceptLaw : X × C -> Real := fun q =>
      if q.2 = concept q.1 then (prior q.1).toReal else 0
    let reducedReal : C -> Y -> Real := fun c y => (reducedKernel c y).toReal
    have markov := markov_of_channel stateConceptLaw reducedReal reducedSum
    have jointLawFormula :
        (fun q : X × (C × Y) =>
          if q.2.1 = concept q.1 then
            (prior q.1).toReal * (kernel q.1 q.2.2).toReal
          else 0) =
          (fun q : X × (C × Y) =>
            stateConceptLaw (q.1, q.2.1) * reducedReal q.2.1 q.2.2) := by
      funext q
      by_cases hc : q.2.1 = concept q.1
      · simp [stateConceptLaw, reducedReal, hc, factorization,
          Function.comp_apply]
      · simp [stateConceptLaw, reducedReal, hc]
    rw [jointLawFormula]
    intro x c y
    specialize markov x c y
    by_cases hc : c = concept x
    · simpa [stateConceptLaw, reducedReal, hc, factorization,
        Function.comp_apply] using markov
    · simpa [stateConceptLaw, reducedReal, hc] using markov
  · intro independent
    have fiberConstant : Function.FactorsThrough kernel concept := by
      intro x x' sameConcept
      apply PMF.ext
      intro y
      rw [← ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top (kernel x) y) (PMF.apply_ne_top (kernel x') y)]
      let jointLaw : X × (C × Y) -> Real := fun q =>
        if q.2.1 = concept q.1 then
          (prior q.1).toReal * (kernel q.1 q.2.2).toReal
        else 0
      let fiberMass : C -> Real := fun c =>
        ∑ z : X, if c = concept z then (prior z).toReal else 0
      let targetMass : C -> Y -> Real := fun c value =>
        ∑ z : X,
          if c = concept z then
            (prior z).toReal * (kernel z value).toReal
          else 0
      have marginalFormula : forall c,
          marginal (yFirstLaw jointLaw) c = fiberMass c := by
        intro c
        simp only [marginal, yFirstLaw, jointLaw, fiberMass,
          Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : c = concept z
        · simp [hz, ← Finset.mul_sum, kernelSum z]
        · simp [hz]
      have xyFormula : forall z c,
          xyProjection jointLaw (z, c) =
            if c = concept z then (prior z).toReal else 0 := by
        intro z c
        simp only [xyProjection, jointLaw]
        by_cases hz : c = concept z
        · simp [hz, ← Finset.mul_sum, kernelSum z]
        · simp [hz]
      have xzFormula : forall c value,
          xzProjection (yFirstLaw jointLaw) (c, value) =
            targetMass c value := by
        intro c value
        simp [xzProjection, yFirstLaw, jointLaw, targetMass]
      have fiberMassPositive : 0 < fiberMass (concept x) := by
        apply Finset.sum_pos'
        · intro z _
          by_cases hz : concept x = concept z
          · simp [hz, ENNReal.toReal_nonneg]
          · simp [hz]
        · exact ⟨x, Finset.mem_univ x, by simp [priorPositive x]⟩
      have atX := independent x (concept x) y
      have atX' := independent x' (concept x) y
      change
        jointLaw (x, (concept x, y)) * marginal (yFirstLaw jointLaw) (concept x) =
          xyProjection jointLaw (x, concept x) *
            xzProjection (yFirstLaw jointLaw) (concept x, y) at atX
      change
        jointLaw (x', (concept x, y)) * marginal (yFirstLaw jointLaw) (concept x) =
          xyProjection jointLaw (x', concept x) *
            xzProjection (yFirstLaw jointLaw) (concept x, y) at atX'
      simp only [jointLaw, marginalFormula, xyFormula, xzFormula, if_pos] at atX
      have sameConcept' : concept x = concept x' := sameConcept
      simp only [jointLaw, marginalFormula, xyFormula, xzFormula,
        sameConcept', if_pos] at atX'
      have priorXPositive := priorPositive x
      have priorX'Positive := priorPositive x'
      rw [← sameConcept] at atX'
      have atXReduced :
          (kernel x y).toReal * fiberMass (concept x) =
            targetMass (concept x) y := by
        apply mul_left_cancel₀ priorXPositive.ne'
        rw [← mul_assoc]
        exact atX
      have atX'Reduced :
          (kernel x' y).toReal * fiberMass (concept x) =
            targetMass (concept x) y := by
        apply mul_left_cancel₀ priorX'Positive.ne'
        rw [← mul_assoc]
        exact atX'
      exact mul_right_cancel₀ fiberMassPositive.ne'
        (atXReduced.trans atX'Reduced.symm)
    letI : Nonempty (PMF Y) :=
      ⟨kernel prior.support_nonempty.some⟩
    exact (Function.factorsThrough_iff (f := concept) kernel).1 fiberConstant

#print axioms positive_prior_sufficiency_iff_conditional_independence

end D5.S3.ConceptDynamics.Completion.PositivePriorConditionalIndependence
