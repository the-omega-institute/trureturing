/- GID: D5/S3/ConceptDynamics/Interpretation/JointLawCertificationValueSeparation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/JointLawCertificationValueSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal decision transcripts can carry separated joint-law certification values. -/

import D5.S3.ConceptDynamics.Interpretation.JointLawExternalizedCertificationMeaning

/- Library-search audit trail (2026-08-29):
   * The exact D5 carrier hit `badGreenMass` is reused rather than redeclared.
   * The exact D5 construction hit `joint_law_externalized_certification_meaning`
     supplies the co-selected Dirac law and independent finite product law.
   * Exact pinned-Mathlib hits `Measure.pi_singleton`,
     `PMF.toMeasure_apply_singleton`, and `Function.FactorsThrough` evaluate the
     two values and state their failure to factor through one transcript.
   * No D5 or Mathlib theorem publicly packages every value-separation clause. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.JointLawCertificationValueSeparation

open D5.S3.ConceptDynamics.Interpretation.JointLawExternalizedCertificationMeaning
open D5.S3.TotalVariation.IndependentSamplingExponentialBound
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- For every nontrivial threshold and positive suite budget, a co-selected
joint law and a deployment-matched product law can realize the same complete
decision transcript while carrying strictly separated bad-green values. Thus
neither the value nor the independent-law metadata is a transcript function. -/
theorem joint_law_certification_value_separation
    (epsilon : Real) (m : Nat)
    (epsilonPositive : 0 < epsilon)
    (epsilonBelowOne : epsilon < 1)
    (suitePositive : 0 < m) :
    let implementation : Bool -> Bool := fun _ => false
    let expected : Bool -> Bool := id
    let World := Measure (Fin m -> Bool) × (Fin m -> Bool)
    let transcript : World -> (Fin m -> Bool) × (Fin m -> Bool) := fun world =>
      (world.2, fun index =>
        decide (implementation (world.2 index) = expected (world.2 index)))
    let certificationValue : World -> Real := fun world =>
      badGreenMass implementation expected world.1
    ∃ deployment : PMF Bool,
      ∃ coSelected independentlySampled : World,
        coSelected.2 = independentlySampled.2 ∧
        (∀ index, coSelected.2 index = false) ∧
        transcript coSelected = transcript independentlySampled ∧
        coSelected.1 = Measure.dirac coSelected.2 ∧
        independentlySampled.1 =
          Measure.pi (fun _ : Fin m => deployment.toMeasure) ∧
        (∑ input : Bool,
          if implementation input = expected input then 0
          else (deployment input).toReal) = (1 + epsilon) / 2 ∧
        epsilon < (∑ input : Bool,
          if implementation input = expected input then 0
          else (deployment input).toReal) ∧
        certificationValue coSelected = 1 ∧
        certificationValue independentlySampled = ((1 - epsilon) / 2) ^ m ∧
        certificationValue independentlySampled <=
          Real.exp (-(epsilon * (m : Real))) ∧
        Real.exp (-(epsilon * (m : Real))) < certificationValue coSelected ∧
        coSelected.1 ≠ independentlySampled.1 ∧
        ¬Function.FactorsThrough certificationValue transcript ∧
        ¬Function.FactorsThrough
          (fun world => world.1 =
            Measure.pi (fun _ : Fin m => deployment.toMeasure))
          transcript := by
  dsimp only
  rcases joint_law_externalized_certification_meaning epsilon m
      epsilonPositive epsilonBelowOne with
    ⟨deployment, coSelected, independentlySampled, sameSuite, allFalse,
      coSelectedLaw, independentLaw, lossValue⟩
  let transcript :
      (Measure (Fin m -> Bool) × (Fin m -> Bool)) ->
        (Fin m -> Bool) × (Fin m -> Bool) := fun world =>
    (world.2, fun index =>
      decide ((fun _ : Bool => false) (world.2 index) =
        (id : Bool -> Bool) (world.2 index)))
  let certificationValue :
      (Measure (Fin m -> Bool) × (Fin m -> Bool)) -> Real := fun world =>
    badGreenMass (fun _ : Bool => false) (id : Bool -> Bool) world.1
  have sameTranscript : transcript coSelected = transcript independentlySampled := by
    simp only [transcript, sameSuite]
  have lossAboveThreshold :
      epsilon < (∑ input : Bool,
        if (fun _ : Bool => false) input = (id : Bool -> Bool) input then 0
        else (deployment input).toReal) := by
    rw [lossValue]
    linarith
  have implementationWrong :
      (fun _ : Bool => false) ≠ (id : Bool -> Bool) := by
    intro equalFunctions
    have atTrue := congrFun equalFunctions true
    simp at atTrue
  have eventIsSingleton :
      {suite : Fin m -> Bool |
          (fun _ : Bool => false) ≠ (id : Bool -> Bool) ∧
            ∀ index, (fun _ : Bool => false) (suite index) =
              (id : Bool -> Bool) (suite index)} =
        {coSelected.2} := by
    ext suite
    constructor
    · rintro ⟨_, suitePasses⟩
      have suiteEquals : suite = coSelected.2 := by
        funext index
        have suiteFalse : suite index = false := by
          simpa using suitePasses index
        exact suiteFalse.trans (allFalse index).symm
      simpa using suiteEquals
    · intro suiteMember
      have suiteEquals : suite = coSelected.2 := by
        simpa using suiteMember
      subst suite
      refine ⟨implementationWrong, ?_⟩
      intro index
      simpa using allFalse index
  have coSelectedMass : certificationValue coSelected = 1 := by
    change badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)
      coSelected.1 = 1
    rw [coSelectedLaw, badGreenMass, eventIsSingleton]
    simp [measureReal_def]
  have trueMass : (deployment true).toReal = (1 + epsilon) / 2 := by
    simpa using lossValue
  have normalizationENNReal : deployment false + deployment true = 1 := by
    simpa [tsum_fintype, add_comm] using deployment.tsum_coe
  have normalizationReal :
      (deployment false).toReal + (deployment true).toReal = 1 := by
    have converted := congrArg ENNReal.toReal normalizationENNReal
    simpa [ENNReal.toReal_add (deployment.apply_ne_top false)
      (deployment.apply_ne_top true)] using converted
  have failureMass : (deployment false).toReal = (1 - epsilon) / 2 := by
    linarith
  have independentMass :
      certificationValue independentlySampled = ((1 - epsilon) / 2) ^ m := by
    change badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)
      independentlySampled.1 = ((1 - epsilon) / 2) ^ m
    rw [independentLaw, badGreenMass, eventIsSingleton,
      measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    have coordinateMass (index : Fin m) :
        (deployment.toMeasure {coSelected.2 index}).toReal =
          (1 - epsilon) / 2 := by
      rw [PMF.toMeasure_apply_singleton deployment (coSelected.2 index)
        (measurableSet_singleton (coSelected.2 index))]
      rw [allFalse index]
      exact failureMass
    simp_rw [coordinateMass]
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
  have independentEnvelope :
      certificationValue independentlySampled <=
        Real.exp (-(epsilon * (m : Real))) := by
    rw [independentMass]
    have halfFailureNonnegative : 0 <= (1 - epsilon) / 2 := by
      linarith
    calc
      ((1 - epsilon) / 2) ^ m <= (1 - epsilon) ^ m := by
        exact pow_le_pow_left₀ halfFailureNonnegative (by linarith) m
      _ <= Real.exp (-(epsilon * (m : Real))) :=
        independent_sampling_exponential_bound epsilon m
          epsilonPositive.le epsilonBelowOne.le
  have positiveBudgetReal : 0 < (m : Real) := by
    exact_mod_cast suitePositive
  have collapsedBeyondEnvelope :
      Real.exp (-(epsilon * (m : Real))) < certificationValue coSelected := by
    rw [coSelectedMass, Real.exp_lt_one_iff]
    nlinarith
  have distinctLaws : coSelected.1 ≠ independentlySampled.1 := by
    intro sameLaws
    have sameMass := congrArg
      (badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)) sameLaws
    change certificationValue coSelected =
      certificationValue independentlySampled at sameMass
    linarith
  have massNotFromTranscript :
      ¬Function.FactorsThrough certificationValue transcript := by
    intro factors
    have sameMass := factors sameTranscript
    linarith
  have coSelectedNotIndependent :
      ¬(coSelected.1 = Measure.pi (fun _ : Fin m => deployment.toMeasure)) := by
    intro coMatchesDeployment
    apply distinctLaws
    exact coMatchesDeployment.trans independentLaw.symm
  have independenceNotFromTranscript :
      ¬Function.FactorsThrough
        (fun world : Measure (Fin m -> Bool) × (Fin m -> Bool) =>
          world.1 = Measure.pi (fun _ : Fin m => deployment.toMeasure))
        transcript := by
    intro factors
    have sameStatus := factors sameTranscript
    change (coSelected.1 = Measure.pi (fun _ : Fin m => deployment.toMeasure)) =
      (independentlySampled.1 =
        Measure.pi (fun _ : Fin m => deployment.toMeasure)) at sameStatus
    apply coSelectedNotIndependent
    rw [sameStatus]
    exact independentLaw
  exact ⟨deployment, coSelected, independentlySampled, sameSuite, allFalse,
    sameTranscript, coSelectedLaw, independentLaw, lossValue,
    lossAboveThreshold, coSelectedMass, independentMass, independentEnvelope,
    collapsedBeyondEnvelope, distinctLaws, massNotFromTranscript,
    independenceNotFromTranscript⟩

#print axioms joint_law_certification_value_separation

end D5.S3.ConceptDynamics.Interpretation.JointLawCertificationValueSeparation
