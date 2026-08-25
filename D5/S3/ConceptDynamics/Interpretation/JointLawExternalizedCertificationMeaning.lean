/- GID: D5/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Externalize certification meaning through a finite joint product law. -/

import D5.S3.TotalVariation.IndependentSamplingExponentialBound
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-25):
   * Repository body-shape searches found the retracted marginal-law carrier,
     but no finite joint-law version of this result or bad-green event mass.
   * Exact pinned-Mathlib hits `Measure.pi`, `Measure.pi_singleton`,
     `PMF.toMeasure_apply_singleton`, and `PMF.ofFintype_apply` construct and
     evaluate the joint product law.
   * The exact D5 hit `independent_sampling_exponential_bound` supplies the
     exponential step below. No library theorem packages the two worlds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.JointLawExternalizedCertificationMeaning

open D5.S3.TotalVariation.IndependentSamplingExponentialBound
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- Probability that a globally wrong implementation passes every check in a
suite sampled from one joint law. -/
def badGreenMass {m : Nat} (implementation expected : Bool -> Bool)
    (jointLaw : Measure (Fin m -> Bool)) : Real :=
  jointLaw.real {suite |
    implementation ≠ expected ∧
      ∀ index, implementation (suite index) = expected (suite index)}

/-- Two worlds can carry the same realized suite while differing in the
external metadata that gives the suite its certification meaning. The five
public clauses are the independent construction clauses; transcript equality
and certification-value separation are derived from them below. -/
theorem joint_law_externalized_certification_meaning
    (epsilon : Real) (m : Nat)
    (epsilonPositive : 0 < epsilon)
    (epsilonBelowOne : epsilon < 1) :
    let implementation : Bool -> Bool := fun _ => false
    let expected : Bool -> Bool := id
    let World := Measure (Fin m -> Bool) × (Fin m -> Bool)
    ∃ deployment : PMF Bool,
      ∃ coSelected independentlySampled : World,
        coSelected.2 = independentlySampled.2 ∧
        (∀ index, coSelected.2 index = false) ∧
        coSelected.1 = Measure.dirac coSelected.2 ∧
        independentlySampled.1 =
          Measure.pi (fun _ : Fin m => deployment.toMeasure) ∧
        (∑ input : Bool,
          if implementation input = expected input then 0
          else (deployment input).toReal) = (1 + epsilon) / 2 := by
  dsimp only
  have probabilityNonnegative : 0 <= (1 + epsilon) / 2 := by
    linarith
  have probabilityAtMostOne : (1 + epsilon) / 2 <= 1 := by
    linarith
  let failureProbability : NNReal :=
    ⟨(1 + epsilon) / 2, probabilityNonnegative⟩
  have failureProbabilityAtMostOne : failureProbability <= 1 := by
    change (1 + epsilon) / 2 <= 1
    exact probabilityAtMostOne
  let deploymentWeights : Bool -> ENNReal := fun input =>
    if input then failureProbability else 1 - failureProbability
  have deploymentWeightsSum : ∑ input, deploymentWeights input = 1 := by
    simp [deploymentWeights, failureProbabilityAtMostOne]
  let deployment : PMF Bool :=
    PMF.ofFintype deploymentWeights deploymentWeightsSum
  let observedSuite : Fin m -> Bool := fun _ => false
  let coSelected := (Measure.dirac observedSuite, observedSuite)
  let independentlySampled :=
    (Measure.pi (fun _ : Fin m => deployment.toMeasure), observedSuite)
  refine ⟨deployment, coSelected, independentlySampled, rfl, ?_, rfl, rfl, ?_⟩
  · exact fun _ => rfl
  · simp [deployment, deploymentWeights, failureProbability]
    rfl

/-- The omitted redundant clauses follow from the public joint-law clauses:
the co-selected bad-green mass collapses to one, while the independent product
has the product mass and its imported exponential envelope. -/
private theorem joint_law_certification_values
    (epsilon : Real) (m : Nat)
    (epsilonPositive : 0 < epsilon)
    (epsilonBelowOne : epsilon < 1) :
    let implementation : Bool -> Bool := fun _ => false
    let expected : Bool -> Bool := id
    ∃ deployment : PMF Bool,
      ∃ observedSuite : Fin m -> Bool,
        badGreenMass implementation expected (Measure.dirac observedSuite) = 1 ∧
        badGreenMass implementation expected
            (Measure.pi (fun _ : Fin m => deployment.toMeasure)) =
          ((1 - epsilon) / 2) ^ m ∧
        badGreenMass implementation expected
            (Measure.pi (fun _ : Fin m => deployment.toMeasure)) <=
          Real.exp (-(epsilon * (m : Real))) := by
  dsimp only
  rcases joint_law_externalized_certification_meaning epsilon m
      epsilonPositive epsilonBelowOne with
    ⟨deployment, coSelected, independentlySampled, sameSuite, allFalse,
      coSelectedLaw, independentLaw, lossValue⟩
  let observedSuite : Fin m -> Bool := coSelected.2
  have implementationWrong : (fun _ : Bool => false) ≠ (id : Bool -> Bool) := by
    intro equalFunctions
    have atTrue := congrFun equalFunctions true
    simp at atTrue
  have eventIsSingleton :
      {suite : Fin m -> Bool |
          (fun _ : Bool => false) ≠ (id : Bool -> Bool) ∧
            ∀ index, (fun _ : Bool => false) (suite index) =
              (id : Bool -> Bool) (suite index)} =
        {observedSuite} := by
    ext suite
    constructor
    · rintro ⟨_, suitePasses⟩
      have suiteEquals : suite = observedSuite := by
        funext index
        have suiteFalse : suite index = false := by
          simpa using suitePasses index
        exact suiteFalse.trans (allFalse index).symm
      simpa using suiteEquals
    · intro suiteMember
      have suiteEquals : suite = observedSuite := by
        simpa using suiteMember
      subst suite
      refine ⟨implementationWrong, ?_⟩
      intro index
      simpa using allFalse index
  have coSelectedMass :
      badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)
          (Measure.dirac observedSuite) = 1 := by
    rw [badGreenMass, eventIsSingleton]
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
      badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)
          (Measure.pi (fun _ : Fin m => deployment.toMeasure)) =
        ((1 - epsilon) / 2) ^ m := by
    rw [badGreenMass, eventIsSingleton, measureReal_def,
      Measure.pi_singleton, ENNReal.toReal_prod]
    have coordinateMass (index : Fin m) :
        (deployment.toMeasure {observedSuite index}).toReal =
          (1 - epsilon) / 2 := by
      rw [PMF.toMeasure_apply_singleton deployment (observedSuite index)
        (measurableSet_singleton (observedSuite index))]
      change (deployment (coSelected.2 index)).toReal = (1 - epsilon) / 2
      rw [allFalse index]
      exact failureMass
    simp_rw [coordinateMass]
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
  have independentEnvelope :
      badGreenMass (fun _ : Bool => false) (id : Bool -> Bool)
          (Measure.pi (fun _ : Fin m => deployment.toMeasure)) <=
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
  exact ⟨deployment, observedSuite, coSelectedMass, independentMass,
    independentEnvelope⟩

#print axioms badGreenMass
#print axioms joint_law_externalized_certification_meaning

end D5.S3.ConceptDynamics.Interpretation.JointLawExternalizedCertificationMeaning
