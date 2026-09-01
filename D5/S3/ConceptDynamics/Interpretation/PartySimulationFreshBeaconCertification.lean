/- GID: D5/S3/ConceptDynamics/Interpretation/PartySimulationFreshBeaconCertification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/PartySimulationFreshBeaconCertification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound simulated approval and fresh-beacon certification. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/- Library-search audit trail (2026-09-02):
   * D5 name and body-shape searches found the canonical arbitrary-carrier
     `measurableTotalVariation`, defined as the supremum of measurable-event
     gaps. The finite-table `totalVariation` is not used here.
   * The existing fresh-checkpoint owner is restricted to countable PMF
     carriers, so the `Measure.pi_pi` product calculation is applied directly
     for the source's general deployment measure.
   * Exact pinned-Mathlib hits `Measure.prod_apply`, `lintegral_mono`,
     `Measure.pi_pi`, `Measure.map_apply`, and `probReal_add_probReal_compl`
     construct and evaluate the source laws.
   * The certificate is a function of the party seed, the co-selected
     implementation passes the same suite, and verifier randomness remains a
     separate product coordinate. No loss, transcript, pushforward, product,
     independent-suite, or total-variation primitive is redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.PartySimulationFreshBeaconCertification

open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open MeasureTheory Set

/-- A certificate computed only from the parties' sampling seed cannot make a
fixed nontrivial guarantee likely under an all-green honest transcript: a bad
implementation selected from the same seed realizes the identical verifier
input, so reliability bounds approval by `delta`. Since the verifier returns a
Boolean tier on every run, the trivial tier consequently has mass at least
`1 - delta`. Taking the suite itself as `Seed`, the deployment product measure
as `seedLaw`, and the identity as `partySuite` realizes honest sampling from
the source deployment law without a support restriction.

For the sufficient direction, each task selects an implementation before the
independent beacon is revealed. The proof disintegrates the task-beacon product
law, applies the deployment product bound to every fixed task, and then
integrates that uniform bound. The public suite map pushes the beacon law
forward, and measurable total variation transports the ideal bound to it. -/
theorem party_simulation_and_fresh_beacon_certification
    {Seed VerifierCoin Input Output Certificate Anchor Task : Type*}
    [MeasurableSpace Seed] [MeasurableSpace VerifierCoin]
    [MeasurableSpace Input] [MeasurableSpace Output] [MeasurableEq Output]
    [MeasurableSpace Certificate]
    [MeasurableSpace Anchor] [MeasurableSpace Task]
    (deployment : Measure Input) [IsProbabilityMeasure deployment]
    (expected : Input -> Output) (expectedMeasurable : Measurable expected)
    (m : Nat) (epsilon delta : Real)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (verifierCoinLaw : Measure VerifierCoin)
    [IsProbabilityMeasure verifierCoinLaw]
    (partySuite : Seed -> Fin m -> Input)
    (partySuiteMeasurable : Measurable partySuite)
    (certificate : Seed -> Certificate)
    (certificateMeasurable : Measurable certificate)
    (verifier : ((Fin m -> Input × Output) × Certificate) -> VerifierCoin -> Bool)
    (verifierMeasurable : Measurable (Function.uncurry verifier))
    (coSelected : Seed -> Input -> Output)
    (taskLaw : Measure Task) [IsProbabilityMeasure taskLaw]
    (anchorLaw : Measure Anchor) [IsProbabilityMeasure anchorLaw]
    (suiteMap : Anchor -> Fin m -> Input) (suiteMapMeasurable : Measurable suiteMap)
    (implementation : Task -> Input -> Output)
    (implementationMeasurable : Measurable (Function.uncurry implementation)) :
    ((forall strategy : Seed -> Input -> Output,
        (seedLaw.prod verifierCoinLaw).real
          {omega |
            verifier
                ((fun index =>
                    (partySuite omega.1 index,
                      strategy omega.1 (partySuite omega.1 index))),
                  certificate omega.1)
                omega.2 = true ∧
              epsilon < deployment.real
                {input | strategy omega.1 input ≠ expected input}} <= delta) ->
      (forall seed index,
        coSelected seed (partySuite seed index) = expected (partySuite seed index)) ->
      (forall seed, epsilon < deployment.real
        {input | coSelected seed input ≠ expected input}) ->
      (seedLaw.prod verifierCoinLaw).real
          {omega |
            verifier
                ((fun index =>
                    (partySuite omega.1 index, expected (partySuite omega.1 index))),
                  certificate omega.1)
                omega.2 = true} <= delta ∧
        1 - delta <=
          (seedLaw.prod verifierCoinLaw).real
            {omega |
              verifier
                  ((fun index =>
                      (partySuite omega.1 index, expected (partySuite omega.1 index))),
                    certificate omega.1)
                  omega.2 = false}) ∧
    (0 <= epsilon -> epsilon <= 1 ->
      (forall task, epsilon < deployment.real
        {input | implementation task input ≠ expected input}) ->
      (taskLaw.prod anchorLaw)
          {taskAnchor | forall index,
            implementation taskAnchor.1 (suiteMap taskAnchor.2 index) =
              expected (suiteMap taskAnchor.2 index)} <=
        ENNReal.ofReal ((1 - epsilon) ^ m) +
          measurableTotalVariation
            (Measure.map suiteMap anchorLaw)
            (Measure.pi (fun _ : Fin m => deployment))) := by
  classical
  constructor
  · intro reliable coSelectedPasses coSelectedBad
    let jointLaw : Measure (Seed × VerifierCoin) :=
      seedLaw.prod verifierCoinLaw
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
              epsilon < deployment.real
                {input | coSelected omega.1 input ≠ expected input}} := by
      ext omega
      simp only [honestGrant, Set.mem_ofPred_eq]
      rw [sameVerifierInput omega]
      simp only [coSelectedBad omega.1, and_true]
    have grantBound : jointLaw.real honestGrant <= delta := by
      rw [grantEventEq]
      exact reliable coSelected
    have honestRecordMeasurable : Measurable (fun seed : Seed =>
        fun index : Fin m =>
          (partySuite seed index, expected (partySuite seed index))) := by
      exact measurable_pi_lambda _ fun index =>
        let suiteAtIndex :=
          (measurable_pi_apply index).comp partySuiteMeasurable
        suiteAtIndex.prodMk (expectedMeasurable.comp suiteAtIndex)
    have honestVerifierInputMeasurable : Measurable (fun omega : Seed × VerifierCoin =>
        (((fun index =>
            (partySuite omega.1 index, expected (partySuite omega.1 index))),
          certificate omega.1), omega.2)) := by
      exact
        ((honestRecordMeasurable.comp measurable_fst).prodMk
            (certificateMeasurable.comp measurable_fst)).prodMk measurable_snd
    have honestDecisionMeasurable : Measurable (fun omega : Seed × VerifierCoin =>
        verifier
            ((fun index =>
                (partySuite omega.1 index, expected (partySuite omega.1 index))),
              certificate omega.1)
            omega.2) :=
      verifierMeasurable.comp honestVerifierInputMeasurable
    have honestGrantMeasurable : MeasurableSet honestGrant := by
      exact honestDecisionMeasurable (measurableSet_singleton true)
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
    let jointLaw : Measure (Task × Anchor) := taskLaw.prod anchorLaw
    let inducedSuiteLaw : Measure (Fin m -> Input) :=
      Measure.map suiteMap anchorLaw
    let idealSuiteLaw : Measure (Fin m -> Input) :=
      Measure.pi (fun _ : Fin m => deployment)
    let allPass (task : Task) : Set (Fin m -> Input) :=
      {suite | forall index,
        implementation task (suite index) = expected (suite index)}
    let jointPass : Set (Task × Anchor) :=
      {taskAnchor | forall index,
        implementation taskAnchor.1 (suiteMap taskAnchor.2 index) =
          expected (suiteMap taskAnchor.2 index)}
    let _ : IsProbabilityMeasure inducedSuiteLaw := by
      dsimp only [inducedSuiteLaw]
      exact Measure.isProbabilityMeasure_map suiteMapMeasurable.aemeasurable
    let _ : IsProbabilityMeasure idealSuiteLaw := by
      dsimp only [idealSuiteLaw]
      infer_instance
    have implementationAtMeasurable (task : Task) :
        Measurable (implementation task) :=
      implementationMeasurable.comp (measurable_const.prodMk measurable_id)
    have allPassMeasurable (task : Task) : MeasurableSet (allPass task) := by
      exact (Measurable.forall fun index =>
        ((implementationAtMeasurable task).comp (measurable_pi_apply index)).eq
          (expectedMeasurable.comp (measurable_pi_apply index))).setOf
    have jointPassMeasurable : MeasurableSet jointPass := by
      exact (Measurable.forall fun index =>
        let sampledInput : Task × Anchor -> Input :=
          fun taskAnchor => suiteMap taskAnchor.2 index
        have sampledInputMeasurable : Measurable sampledInput :=
          (measurable_pi_apply index).comp (suiteMapMeasurable.comp measurable_snd)
        (implementationMeasurable.comp
            (measurable_fst.prodMk sampledInputMeasurable)).eq
          (expectedMeasurable.comp sampledInputMeasurable)).setOf
    have sectionMass (task : Task) :
        anchorLaw (Prod.mk task ⁻¹' jointPass) =
          inducedSuiteLaw (allPass task) := by
      rw [show Prod.mk task ⁻¹' jointPass = suiteMap ⁻¹' allPass task by
        ext anchor
        simp [jointPass, allPass]]
      exact (Measure.map_apply suiteMapMeasurable (allPassMeasurable task)).symm
    have idealBound (task : Task) :
        idealSuiteLaw (allPass task) <= ENNReal.ofReal ((1 - epsilon) ^ m) := by
      let passSet : Set Input :=
        {input | implementation task input = expected input}
      let failureSet : Set Input :=
        {input | implementation task input ≠ expected input}
      have passMeasurable : MeasurableSet passSet := by
        exact measurableSet_eq_fun (implementationAtMeasurable task) expectedMeasurable
      have failureMeasurable : MeasurableSet failureSet := by
        rw [show failureSet = passSetᶜ by
          ext input
          simp [failureSet, passSet]]
        exact passMeasurable.compl
      have allPassRectangle :
          allPass task = Set.pi Set.univ (fun _ : Fin m => passSet) := by
        ext suite
        simp [allPass, passSet]
      have idealExact :
          idealSuiteLaw.real (allPass task) = (deployment.real passSet) ^ m := by
        rw [measureReal_def, allPassRectangle]
        simp only [idealSuiteLaw, Measure.pi_pi, ENNReal.toReal_prod]
        simp [measureReal_def]
      have passIsFailureComplement : passSet = failureSetᶜ := by
        ext input
        simp [passSet, failureSet]
      have passFailureMass :=
        probReal_add_probReal_compl (μ := deployment) failureMeasurable
      have passMassAtMost : deployment.real passSet <= 1 - epsilon := by
        rw [passIsFailureComplement]
        linarith [lossAbove task]
      have idealRealBound :
          idealSuiteLaw.real (allPass task) <= (1 - epsilon) ^ m := by
        rw [idealExact]
        exact pow_le_pow_left₀ measureReal_nonneg passMassAtMost m
      rw [← ENNReal.ofReal_toReal (measure_ne_top idealSuiteLaw (allPass task))]
      exact ENNReal.ofReal_le_ofReal idealRealBound
    have eventGap (task : Task) :
        inducedSuiteLaw (allPass task) - idealSuiteLaw (allPass task) <=
          measurableTotalVariation inducedSuiteLaw idealSuiteLaw := by
      unfold measurableTotalVariation
      exact (le_max_left
          (inducedSuiteLaw (allPass task) - idealSuiteLaw (allPass task))
          (idealSuiteLaw (allPass task) - inducedSuiteLaw (allPass task))).trans
        (le_iSup
          (fun event : {event : Set (Fin m -> Input) // MeasurableSet event} =>
            max (inducedSuiteLaw event.1 - idealSuiteLaw event.1)
              (idealSuiteLaw event.1 - inducedSuiteLaw event.1))
          ⟨allPass task, allPassMeasurable task⟩)
    have inducedBound (task : Task) :
        inducedSuiteLaw (allPass task) <=
          ENNReal.ofReal ((1 - epsilon) ^ m) +
            measurableTotalVariation inducedSuiteLaw idealSuiteLaw := by
      calc
        inducedSuiteLaw (allPass task) <=
            measurableTotalVariation inducedSuiteLaw idealSuiteLaw +
              idealSuiteLaw (allPass task) :=
          tsub_le_iff_right.mp (eventGap task)
        _ <= measurableTotalVariation inducedSuiteLaw idealSuiteLaw +
              ENNReal.ofReal ((1 - epsilon) ^ m) :=
          add_le_add (le_refl _) (idealBound task)
        _ = ENNReal.ofReal ((1 - epsilon) ^ m) +
              measurableTotalVariation inducedSuiteLaw idealSuiteLaw := add_comm _ _
    change jointLaw jointPass <=
      ENNReal.ofReal ((1 - epsilon) ^ m) +
        measurableTotalVariation inducedSuiteLaw idealSuiteLaw
    rw [show jointLaw jointPass =
        ∫⁻ task, anchorLaw (Prod.mk task ⁻¹' jointPass) ∂taskLaw by
      exact Measure.prod_apply jointPassMeasurable]
    calc
      (∫⁻ task, anchorLaw (Prod.mk task ⁻¹' jointPass) ∂taskLaw) =
          ∫⁻ task, inducedSuiteLaw (allPass task) ∂taskLaw :=
        lintegral_congr sectionMass
      _ <= ∫⁻ _ : Task,
          ENNReal.ofReal ((1 - epsilon) ^ m) +
            measurableTotalVariation inducedSuiteLaw idealSuiteLaw ∂taskLaw :=
        lintegral_mono inducedBound
      _ = ENNReal.ofReal ((1 - epsilon) ^ m) +
            measurableTotalVariation inducedSuiteLaw idealSuiteLaw := by
        simp only [lintegral_const, measure_univ, mul_one]

#print axioms party_simulation_and_fresh_beacon_certification

end D5.S3.ConceptDynamics.Interpretation.PartySimulationFreshBeaconCertification
