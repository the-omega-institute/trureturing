/- GID: D5/S3/ConceptDynamics/Interpretation/PartySimulationFreshBeaconCertification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/PartySimulationFreshBeaconCertification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound simulated approval and fresh-beacon certification. -/

import D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee
import D5.S3.TotalVariation.Metric
import Mathlib.MeasureTheory.Measure.Prod

/- Library-search audit trail (2026-09-02):
   * D5 name and body-shape searches found the Boolean joint-law separation
     witnesses, the general fresh-checkpoint guarantee, transcript-law
     invariance, and the finite event characterization of total variation.
     None states both halves of the source theorem under one public signature.
   * `fresh_independent_checkpoint_deployment_guarantee` supplies the exact
     product-law all-pass mass. `total_variation_eq_sup_event_gap` supplies the
     perturbation from the ideal suite law to the beacon-induced suite law.
   * Exact pinned-Mathlib hits `Measure.prod`, `Measure.pi`, `Measure.map_apply`,
     `measureReal_prod_prod`, `sum_measureReal_singleton`, and
     `probReal_add_probReal_compl` construct and evaluate the source laws.
   * The certificate is a function of the party seed, the co-selected
     implementation passes the same suite, and verifier randomness remains a
     separate product coordinate. No loss, transcript, pushforward, product,
     independent-suite, or total-variation primitive is redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.PartySimulationFreshBeaconCertification

open D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker
open MeasureTheory Set

/-- A certificate computed only from the parties' sampling seed cannot make a
fixed nontrivial guarantee likely under an all-green honest transcript: a bad
implementation selected from the same seed realizes the identical verifier
input, so reliability bounds approval by `delta`. Since the verifier returns a
Boolean tier on every run, the trivial tier consequently has mass at least
`1 - delta`.

For the sufficient direction, the implementation is fixed before the beacon.
The task and beacon have their actual product law, the ideal suite has the
finite deployment product law, and the public fixed suite map pushes the beacon
law forward. A bad implementation's all-pass mass is at most the ideal
`(1 - epsilon) ^ m` term plus the finite total-variation discrepancy. -/
theorem party_simulation_and_fresh_beacon_certification
    {Seed VerifierCoin Input Output Certificate Anchor Task : Type*}
    [Finite Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    [Finite VerifierCoin] [MeasurableSpace VerifierCoin]
    [MeasurableSingletonClass VerifierCoin]
    [Fintype Input] [MeasurableSpace Input] [MeasurableSingletonClass Input]
    [Finite Anchor] [MeasurableSpace Anchor] [MeasurableSingletonClass Anchor]
    [Finite Task] [MeasurableSpace Task] [MeasurableSingletonClass Task]
    (deployment : PMF Input) (expected : Input -> Output)
    (m : Nat) (epsilon delta : Real)
    (seedLaw : PMF Seed) (verifierCoinLaw : PMF VerifierCoin)
    (partySuite : Seed -> Fin m -> Input)
    (certificate : Seed -> Certificate)
    (verifier : ((Fin m -> Input × Output) × Certificate) -> VerifierCoin -> Bool)
    (coSelected : Seed -> Input -> Output)
    (taskLaw : PMF Task) (anchorLaw : PMF Anchor)
    (suiteMap : Anchor -> Fin m -> Input)
    (implementation : Input -> Output) :
    ((forall strategy : Seed -> Input -> Output,
        (seedLaw.toMeasure.prod verifierCoinLaw.toMeasure).real
          {omega |
            verifier
                ((fun index =>
                    (partySuite omega.1 index,
                      strategy omega.1 (partySuite omega.1 index))),
                  certificate omega.1)
                omega.2 = true ∧
              epsilon < deployment.toMeasure.real
                {input | strategy omega.1 input ≠ expected input}} <= delta) ->
      (forall seed index,
        coSelected seed (partySuite seed index) = expected (partySuite seed index)) ->
      (forall seed, epsilon < deployment.toMeasure.real
        {input | coSelected seed input ≠ expected input}) ->
      (seedLaw.toMeasure.prod verifierCoinLaw.toMeasure).real
          {omega |
            verifier
                ((fun index =>
                    (partySuite omega.1 index, expected (partySuite omega.1 index))),
                  certificate omega.1)
                omega.2 = true} <= delta ∧
        1 - delta <=
          (seedLaw.toMeasure.prod verifierCoinLaw.toMeasure).real
            {omega |
              verifier
                  ((fun index =>
                      (partySuite omega.1 index, expected (partySuite omega.1 index))),
                    certificate omega.1)
                  omega.2 = false}) ∧
    (0 <= epsilon -> epsilon <= 1 ->
      epsilon < deployment.toMeasure.real
        {input | implementation input ≠ expected input} ->
      (taskLaw.toMeasure.prod anchorLaw.toMeasure).real
          {taskAnchor | forall index,
            implementation (suiteMap taskAnchor.2 index) =
              expected (suiteMap taskAnchor.2 index)} <=
        (1 - epsilon) ^ m +
          totalVariation
            (fun suite =>
              (Measure.map suiteMap anchorLaw.toMeasure).real {suite})
            (fun suite =>
              (Measure.pi (fun _ : Fin m => deployment.toMeasure)).real {suite})) := by
  classical
  constructor
  · intro reliable coSelectedPasses coSelectedBad
    let jointLaw : Measure (Seed × VerifierCoin) :=
      seedLaw.toMeasure.prod verifierCoinLaw.toMeasure
    let honestGrant : Set (Seed × VerifierCoin) :=
      {omega |
        verifier
            ((fun index =>
                (partySuite omega.1 index, expected (partySuite omega.1 index))),
              certificate omega.1)
            omega.2 = true}
    let trivialTier : Set (Seed × VerifierCoin) :=
      {omega |
        verifier
            ((fun index =>
                (partySuite omega.1 index, expected (partySuite omega.1 index))),
              certificate omega.1)
            omega.2 = false}
    have sameVerifierInput (omega : Seed × VerifierCoin) :
        ((fun index =>
            (partySuite omega.1 index, expected (partySuite omega.1 index))),
          certificate omega.1) =
        ((fun index =>
            (partySuite omega.1 index,
              coSelected omega.1 (partySuite omega.1 index))),
          certificate omega.1) := by
      apply Prod.ext
      · funext index
        exact Prod.ext rfl (coSelectedPasses omega.1 index).symm
      · rfl
    have grantEventEq :
        honestGrant =
          {omega |
            verifier
                ((fun index =>
                    (partySuite omega.1 index,
                      coSelected omega.1 (partySuite omega.1 index))),
                  certificate omega.1)
                omega.2 = true ∧
              epsilon < deployment.toMeasure.real
                {input | coSelected omega.1 input ≠ expected input}} := by
      ext omega
      simp only [honestGrant, Set.mem_ofPred_eq]
      rw [sameVerifierInput omega]
      simp only [coSelectedBad omega.1, and_true]
    have grantBound : jointLaw.real honestGrant <= delta := by
      rw [grantEventEq]
      exact reliable coSelected
    have honestGrantMeasurable : MeasurableSet honestGrant :=
      honestGrant.to_countable.measurableSet
    have trivialIsComplement : trivialTier = honestGrantᶜ := by
      ext omega
      simp [trivialTier, honestGrant]
    have totalMass := probReal_add_probReal_compl
      (μ := jointLaw) honestGrantMeasurable
    refine ⟨by simpa [jointLaw, honestGrant] using grantBound, ?_⟩
    change 1 - delta <= jointLaw.real trivialTier
    rw [trivialIsComplement]
    linarith
  · intro epsilonNonnegative epsilonAtMostOne lossAbove
    let jointLaw : Measure (Task × Anchor) :=
      taskLaw.toMeasure.prod anchorLaw.toMeasure
    let inducedSuiteLaw : Measure (Fin m -> Input) :=
      Measure.map suiteMap anchorLaw.toMeasure
    let idealSuiteLaw : Measure (Fin m -> Input) :=
      Measure.pi (fun _ : Fin m => deployment.toMeasure)
    let allPass : Set (Fin m -> Input) :=
      {suite | forall index,
        implementation (suite index) = expected (suite index)}
    let jointPass : Set (Task × Anchor) :=
      {taskAnchor | forall index,
        implementation (suiteMap taskAnchor.2 index) =
          expected (suiteMap taskAnchor.2 index)}
    have suiteMapMeasurable : Measurable suiteMap := measurable_of_finite _
    have allPassMeasurable : MeasurableSet allPass :=
      allPass.to_countable.measurableSet
    have jointPassEq :
        jointPass = Set.univ ×ˢ (suiteMap ⁻¹' allPass) := by
      ext taskAnchor
      simp [jointPass, allPass]
    have actualJointEq : jointLaw.real jointPass = inducedSuiteLaw.real allPass := by
      rw [jointPassEq]
      simp only [jointLaw, measureReal_prod_prod]
      rw [show taskLaw.toMeasure.real Set.univ = 1 by simp [measureReal_def], one_mul]
      rw [show
        anchorLaw.toMeasure.real (suiteMap ⁻¹' allPass) =
            inducedSuiteLaw.real allPass by
          simp only [inducedSuiteLaw, measureReal_def,
            Measure.map_apply suiteMapMeasurable allPassMeasurable]]
    rcases fresh_independent_checkpoint_deployment_guarantee
        deployment implementation expected m epsilon epsilonNonnegative
        epsilonAtMostOne lossAbove.le with
      ⟨idealExact, _idealExponentialBound⟩
    have idealExact' :
        idealSuiteLaw.real allPass =
          (deployment.toMeasure.real
            {input | implementation input = expected input}) ^ m := by
      simpa [idealSuiteLaw, allPass] using idealExact
    let passSet : Set Input :=
      {input | implementation input = expected input}
    let failureSet : Set Input :=
      {input | implementation input ≠ expected input}
    have failureMeasurable : MeasurableSet failureSet :=
      failureSet.to_countable.measurableSet
    have passIsFailureComplement : passSet = failureSetᶜ := by
      ext input
      simp [passSet, failureSet]
    have passFailureMass := probReal_add_probReal_compl
      (μ := deployment.toMeasure) failureMeasurable
    have passMassAtMost :
        deployment.toMeasure.real passSet <= 1 - epsilon := by
      rw [passIsFailureComplement]
      linarith
    have idealBound : idealSuiteLaw.real allPass <= (1 - epsilon) ^ m := by
      rw [idealExact']
      change
        (deployment.toMeasure.real passSet) ^ m <= (1 - epsilon) ^ m
      exact pow_le_pow_left₀ measureReal_nonneg passMassAtMost m
    let p : (Fin m -> Input) -> Real := fun suite => inducedSuiteLaw.real {suite}
    let q : (Fin m -> Input) -> Real := fun suite => idealSuiteLaw.real {suite}
    have pMass : (∑ suite, p suite) = 1 := by
      have singletonSum := sum_measureReal_singleton
        (μ := inducedSuiteLaw) (Finset.univ : Finset (Fin m -> Input))
      calc
        (∑ suite, p suite) = inducedSuiteLaw.real Set.univ := by
          simpa only [p, Finset.coe_univ] using singletonSum
        _ = 1 := by
          simp [inducedSuiteLaw, measureReal_def,
            Measure.map_apply suiteMapMeasurable MeasurableSet.univ]
    have qMass : (∑ suite, q suite) = 1 := by
      have singletonSum := sum_measureReal_singleton
        (μ := idealSuiteLaw) (Finset.univ : Finset (Fin m -> Input))
      calc
        (∑ suite, q suite) = idealSuiteLaw.real Set.univ := by
          simpa only [q, Finset.coe_univ] using singletonSum
        _ = 1 := by simp [idealSuiteLaw, measureReal_def]
    let passFinset : Finset (Fin m -> Input) :=
      Finset.univ.filter fun suite => forall index,
        implementation (suite index) = expected (suite index)
    have pEvent :
        (∑ suite ∈ passFinset, p suite) = inducedSuiteLaw.real allPass := by
      have singletonSum := sum_measureReal_singleton
        (μ := inducedSuiteLaw) passFinset
      calc
        (∑ suite ∈ passFinset, p suite) =
            inducedSuiteLaw.real (passFinset : Set (Fin m -> Input)) := by
          simpa only [p] using singletonSum
        _ = inducedSuiteLaw.real allPass := by
          congr 1
          ext suite
          simp [passFinset, allPass]
    have qEvent :
        (∑ suite ∈ passFinset, q suite) = idealSuiteLaw.real allPass := by
      have singletonSum := sum_measureReal_singleton
        (μ := idealSuiteLaw) passFinset
      calc
        (∑ suite ∈ passFinset, q suite) =
            idealSuiteLaw.real (passFinset : Set (Fin m -> Input)) := by
          simpa only [q] using singletonSum
        _ = idealSuiteLaw.real allPass := by
          congr 1
          ext suite
          simp [passFinset, allPass]
    have eventGap :
        |inducedSuiteLaw.real allPass - idealSuiteLaw.real allPass| <=
          totalVariation p q := by
      have greatest := total_variation_eq_sup_event_gap p q (pMass.trans qMass.symm)
      have gap := greatest.2 ⟨passFinset, rfl⟩
      change
        |(∑ suite ∈ passFinset, p suite) - (∑ suite ∈ passFinset, q suite)| <=
          totalVariation p q at gap
      rwa [pEvent, qEvent] at gap
    have inducedBound :
        inducedSuiteLaw.real allPass <=
          idealSuiteLaw.real allPass + totalVariation p q := by
      linarith [le_abs_self
        (inducedSuiteLaw.real allPass - idealSuiteLaw.real allPass)]
    change jointLaw.real jointPass <= (1 - epsilon) ^ m + totalVariation p q
    rw [actualJointEq]
    exact inducedBound.trans (add_le_add idealBound (le_refl _))

#print axioms party_simulation_and_fresh_beacon_certification

end D5.S3.ConceptDynamics.Interpretation.PartySimulationFreshBeaconCertification
