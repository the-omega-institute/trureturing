/- GID: D5/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One transcript can carry collapsed or independent certification value. -/

import D5.S3.TotalVariation.IndependentSamplingExponentialBound
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-25):
   * The required interface and contract-family probe found no exact theorem
     about two sampling worlds with one realized transcript and unequal
     certification values.
   * `ProvenanceAdmissionCountermodel` has the adjacent equal-content/opposite-
     admission result, but its report carrier does not construct deployment
     loss or the independent-sampling exponential value, so it is not wrapped.
   * Body-shape searches for Bernoulli suite laws, transcript factorization,
     co-selection, and independently sampled certification found no D5 theorem
     with the public clauses below.
   * Exact pinned-Mathlib hits `PMF.bernoulli_apply`, `Finset.prod_const`, and
     `Real.exp_lt_one_iff` evaluate the constructed model. The repository hit
     `independent_sampling_exponential_bound` supplies the exponential step
     and is applied directly. No library theorem packages both worlds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.ExternalizedCertificationMeaning

open D5.S3.TotalVariation.IndependentSamplingExponentialBound
open scoped BigOperators

/-- For every nontrivial loss threshold and positive suite budget, there are a
co-selected suite world and a deployment-matched independently sampled world.
They realize the same all-green bit transcript, while the co-selected bad-green
mass is one and the independent bad-green mass has the stated exponential
bound. Neither that mass nor the independent-sampling precondition factors
through the transcript. -/
theorem externalized_certification_meaning
    (epsilon : ℝ) (m : ℕ)
    (epsilonPositive : 0 < epsilon)
    (epsilonBelowOne : epsilon < 1)
    (suitePositive : 0 < m) :
    let implementation : Bool -> Bool := fun _ => false
    let expected : Bool -> Bool := id
    let World := (Fin m -> PMF Bool) × (Fin m -> Bool)
    let transcript : World -> Fin m -> Bool := fun world index =>
      decide (implementation (world.2 index) = expected (world.2 index))
    let badGreenMass : World -> ℝ := fun world =>
      ∏ index, ((world.1 index) false).toReal
    ∃ deployment : PMF Bool,
      ∃ coSelected independentlySampled : World,
        coSelected.2 = independentlySampled.2 ∧
        (∀ index, coSelected.2 index = false) ∧
        transcript coSelected = transcript independentlySampled ∧
        (∀ index, coSelected.1 index = PMF.pure (coSelected.2 index)) ∧
        (∀ index, independentlySampled.1 index = deployment) ∧
        (∑ input : Bool,
          if implementation input = expected input then 0
          else (deployment input).toReal) = (1 + epsilon) / 2 ∧
        epsilon < (∑ input : Bool,
          if implementation input = expected input then 0
          else (deployment input).toReal) ∧
        badGreenMass coSelected = 1 ∧
        badGreenMass independentlySampled = ((1 - epsilon) / 2) ^ m ∧
        badGreenMass independentlySampled <=
          Real.exp (-(epsilon * (m : ℝ))) ∧
        Real.exp (-(epsilon * (m : ℝ))) < badGreenMass coSelected ∧
        coSelected.1 ≠ independentlySampled.1 ∧
        ¬Function.FactorsThrough badGreenMass transcript ∧
        ¬Function.FactorsThrough
          (fun world => ∀ index, world.1 index = deployment)
          transcript := by
  dsimp only
  have probabilityNonnegative : 0 <= (1 + epsilon) / 2 := by
    linarith
  let failureProbability : NNReal :=
    ⟨(1 + epsilon) / 2, probabilityNonnegative⟩
  have failureProbabilityAtMostOne : failureProbability <= 1 := by
    change (1 + epsilon) / 2 <= 1
    linarith
  let deployment : PMF Bool :=
    PMF.bernoulli failureProbability failureProbabilityAtMostOne
  let observedSuite : Fin m -> Bool := fun _ => false
  let coSelectedLaws : Fin m -> PMF Bool := fun _ => PMF.pure false
  let independentLaws : Fin m -> PMF Bool := fun _ => deployment
  let coSelected := (coSelectedLaws, observedSuite)
  let independentlySampled := (independentLaws, observedSuite)
  let transcript : ((Fin m -> PMF Bool) × (Fin m -> Bool)) -> Fin m -> Bool :=
    fun world index =>
      decide ((fun _ : Bool => false) (world.2 index) =
        (id : Bool -> Bool) (world.2 index))
  let badGreenMass : ((Fin m -> PMF Bool) × (Fin m -> Bool)) -> ℝ :=
    fun world => ∏ index, ((world.1 index) false).toReal
  have sameSuite : coSelected.2 = independentlySampled.2 := rfl
  have allGreen : ∀ index, coSelected.2 index = false := fun _ => rfl
  have sameTranscript : transcript coSelected = transcript independentlySampled := rfl
  have coSelectedLaw :
      ∀ index, coSelected.1 index = PMF.pure (coSelected.2 index) :=
    fun _ => rfl
  have independentLaw :
      ∀ index, independentlySampled.1 index = deployment :=
    fun _ => rfl
  have lossValue :
      (∑ input : Bool,
        if (fun _ : Bool => false) input = (id : Bool -> Bool) input then 0
        else (deployment input).toReal) = (1 + epsilon) / 2 := by
    simp [deployment, PMF.bernoulli_apply, failureProbability]
    rfl
  have lossAboveThreshold :
      epsilon < (∑ input : Bool,
        if (fun _ : Bool => false) input = (id : Bool -> Bool) input then 0
        else (deployment input).toReal) := by
    rw [lossValue]
    linarith
  have coSelectedMass : badGreenMass coSelected = 1 := by
    simp [badGreenMass, coSelected, coSelectedLaws]
  have independentMass :
      badGreenMass independentlySampled = ((1 - epsilon) / 2) ^ m := by
    simp [badGreenMass, independentlySampled, independentLaws, deployment,
      failureProbability, failureProbabilityAtMostOne]
    rw [PMF.bernoulli_apply failureProbabilityAtMostOne false]
    rw [Bool.cond_false, ENNReal.coe_toReal,
      NNReal.coe_sub failureProbabilityAtMostOne]
    change (1 - (1 + epsilon) / 2) ^ m = ((1 - epsilon) / 2) ^ m
    ring
  have halfFailureNonnegative : 0 <= (1 - epsilon) / 2 := by
    linarith
  have independentEnvelope :
      badGreenMass independentlySampled <=
        Real.exp (-(epsilon * (m : ℝ))) := by
    rw [independentMass]
    calc
      ((1 - epsilon) / 2) ^ m <= (1 - epsilon) ^ m := by
        exact pow_le_pow_left₀ halfFailureNonnegative (by linarith) m
      _ <= Real.exp (-(epsilon * (m : ℝ))) :=
        independent_sampling_exponential_bound epsilon m
          epsilonPositive.le epsilonBelowOne.le
  have positiveBudgetReal : 0 < (m : ℝ) := by
    exact_mod_cast suitePositive
  have collapsedBeyondEnvelope :
      Real.exp (-(epsilon * (m : ℝ))) < badGreenMass coSelected := by
    rw [coSelectedMass, Real.exp_lt_one_iff]
    nlinarith
  have distinctLaws : coSelected.1 ≠ independentlySampled.1 := by
    intro sameLaws
    have sameMass : badGreenMass coSelected = badGreenMass independentlySampled :=
      congrArg (fun laws => ∏ index, ((laws index) false).toReal) sameLaws
    linarith
  have massNotFromTranscript :
      ¬Function.FactorsThrough badGreenMass transcript := by
    intro factors
    have sameMass := factors sameTranscript
    linarith
  have coSelectedNotIndependent :
      ¬(∀ index, coSelected.1 index = deployment) := by
    intro coMatchesDeployment
    apply distinctLaws
    funext index
    exact (coMatchesDeployment index).trans (independentLaw index).symm
  have independenceNotFromTranscript :
      ¬Function.FactorsThrough
        (fun world => ∀ index, world.1 index = deployment)
        transcript := by
    intro factors
    have sameStatus := factors sameTranscript
    change (∀ index, coSelected.1 index = deployment) =
      (∀ index, independentlySampled.1 index = deployment) at sameStatus
    apply coSelectedNotIndependent
    rw [sameStatus]
    exact independentLaw
  exact ⟨deployment, coSelected, independentlySampled, sameSuite, allGreen,
    sameTranscript, coSelectedLaw, independentLaw, lossValue,
    lossAboveThreshold, coSelectedMass, independentMass, independentEnvelope,
    collapsedBeyondEnvelope, distinctLaws, massNotFromTranscript,
    independenceNotFromTranscript⟩

#print axioms externalized_certification_meaning

end D5.S3.ConceptDynamics.Interpretation.ExternalizedCertificationMeaning
