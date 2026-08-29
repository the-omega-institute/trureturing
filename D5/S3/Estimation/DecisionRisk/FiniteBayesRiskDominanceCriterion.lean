/- GID: D5/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/FiniteBayesRiskDominanceCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite stochastic postprocessing is equivalent to universal Bayes-risk dominance. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/- Library-search audit trail (2026-08-30):
   * The exact D5 hit `bayesRisk_le_of_blackwellDominates` proves only the
     postprocessing-to-risk direction for measurable kernels, so it cannot own
     the biconditional below.
   * The finite primitives `IsRowStochastic`, `FiniteMarkovKernel`,
     `channelOutput`, and `finiteBayesCost` are imported from their canonical
     D5 owners rather than redeclared. The only experiment-level risk primitive
     found, `finiteBayesRisk`, applies `ENNReal.ofReal` before its infimum and
     therefore cannot express the source's arbitrary real-valued losses.
   * Pinned Mathlib has the exact forward component
     `ProbabilityTheory.bayesRisk_le_bayesRisk_comp`, but no finite converse.
     The converse below directly applies `geometric_hahn_banach_closed_point`,
     `isCompact_stdSimplex`, and `convex_stdSimplex`.
   * Body-shape searches for products of row simplexes and finite linear
     certificates found `isCompact_univ_pi`, `convex_pi`, and the local D5
     separation precedents `FiniteExpectationTableSeparation` and
     `FiniteRealizationCertificate`.
-/

noncomputable section

open Set
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.FiniteBayesRiskDominanceCriterion

universe u

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

private theorem continuous_linear_expansion
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (functional : (I -> J -> Real) →L[Real] Real)
    (table : I -> J -> Real) :
    functional table =
      ∑ i, ∑ j,
        functional (Pi.single i (Pi.single j 1)) * table i j := by
  classical
  have tableExpansion :
      table = ∑ i, ∑ j, table i j • Pi.single i (Pi.single j 1) := by
    funext i j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp_rw [ite_apply, Pi.single_apply, mul_ite, mul_zero]
    simp only [Pi.zero_apply, mul_zero, mul_one]
    symm
    calc
      (∑ x, ∑ y,
          if i = x then if j = y then table x y else 0 else 0) =
          ∑ x, if i = x then table x j else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : i = x
        · simp only [h, if_true]
          exact Fintype.sum_ite_eq j (fun y => table x y)
        · simp [h]
      _ = table i j := Fintype.sum_ite_eq i (fun x => table x j)
  conv_lhs => rw [tableExpansion]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  exact mul_comm (table i j)
    (functional (Pi.single i (Pi.single j 1)))

private theorem finite_bayes_cost_uniform_separator
    {State Observation Action : Type*}
    [Fintype State] [Nonempty State]
    [Fintype Observation] [Fintype Action]
    (experiment : State -> Observation -> Real)
    (decision : Observation -> Action -> Real)
    (experimentStochastic : IsRowStochastic experiment)
    (decisionStochastic : IsRowStochastic decision)
    (coefficient : State -> Action -> Real)
    (constant : Real) :
    let prior : State -> Real := fun _ => (Fintype.card State : Real)⁻¹
    let loss : State -> Action -> Real := fun state action =>
      constant - (Fintype.card State : Real) * coefficient state action
    finiteBayesCost prior loss experiment decision =
      constant -
        ∑ state, ∑ action,
          coefficient state action *
            channelOutput decision (experiment state) action := by
  classical
  dsimp only
  have cardNonzero : (Fintype.card State : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have outputStochastic :
      IsRowStochastic (fun state action =>
        channelOutput decision (experiment state) action) := by
    constructor
    · intro state action
      unfold channelOutput
      exact Finset.sum_nonneg fun observation _ =>
        mul_nonneg (experimentStochastic.1 state observation)
          (decisionStochastic.1 observation action)
    · intro state
      unfold channelOutput
      rw [Finset.sum_comm]
      calc
        (∑ observation, ∑ action,
            experiment state observation * decision observation action) =
            ∑ observation,
              experiment state observation * ∑ action, decision observation action := by
                apply Finset.sum_congr rfl
                intro observation _
                rw [Finset.mul_sum]
        _ = ∑ observation, experiment state observation := by
              apply Finset.sum_congr rfl
              intro observation _
              rw [decisionStochastic.2 observation, mul_one]
        _ = 1 := experimentStochastic.2 state
  unfold finiteBayesCost
  calc
    (∑ state, (Fintype.card State : Real)⁻¹ *
        ∑ action,
          channelOutput decision (experiment state) action *
            (constant - (Fintype.card State : Real) *
              coefficient state action)) =
        ∑ state,
          ((Fintype.card State : Real)⁻¹ * constant -
            ∑ action,
              coefficient state action *
                channelOutput decision (experiment state) action) := by
          apply Finset.sum_congr rfl
          intro state _
          have outputMass := outputStochastic.2 state
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          rw [← Finset.sum_mul]
          rw [outputMass, one_mul]
          have scaledCoefficient :
              (∑ action,
                channelOutput decision (experiment state) action *
                  ((Fintype.card State : Real) * coefficient state action)) =
                (Fintype.card State : Real) *
                  ∑ action,
                    coefficient state action *
                      channelOutput decision (experiment state) action := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro action _
            ring
          rw [scaledCoefficient]
          field_simp [cardNonzero]
    _ = constant -
        ∑ state, ∑ action,
          coefficient state action *
            channelOutput decision (experiment state) action := by
          rw [Finset.sum_sub_distrib]
          simp [cardNonzero]

/-- For finite experiments on a nonempty parameter set, an exact randomized
postprocessing exists precisely when every finite prior, action space, and
real-valued loss gives the source experiment no larger optimal Bayes risk. -/
theorem finite_bayes_risk_dominance_iff_postprocessing
    {State SourceObservation TargetObservation : Type u}
    [Fintype State] [Nonempty State]
    [Fintype SourceObservation] [Fintype TargetObservation]
    (source : State -> SourceObservation -> Real)
    (target : State -> TargetObservation -> Real)
    (sourceStochastic : IsRowStochastic source)
    (targetStochastic : IsRowStochastic target) :
    (∃ simulator : FiniteMarkovKernel SourceObservation TargetObservation,
      target = fun state => channelOutput simulator.1 (source state)) ↔
    ∀ (Action : Type u) [Fintype Action]
      (prior : State -> Real) (loss : State -> Action -> Real),
      ((∀ state, 0 ≤ prior state) ∧ (∑ state, prior state) = 1) ->
      sInf (Set.range fun decision : FiniteMarkovKernel SourceObservation Action =>
        finiteBayesCost prior loss source decision.1) ≤
      sInf (Set.range fun decision : FiniteMarkovKernel TargetObservation Action =>
        finiteBayesCost prior loss target decision.1) := by
  classical
  have sourceObservationNonempty : Nonempty SourceObservation := by
    by_contra noObservation
    letI : IsEmpty SourceObservation := not_nonempty_iff.mp noObservation
    let state : State := Classical.choice (inferInstance : Nonempty State)
    have rowMass := sourceStochastic.2 state
    simpa using rowMass
  have targetObservationNonempty : Nonempty TargetObservation := by
    by_contra noObservation
    letI : IsEmpty TargetObservation := not_nonempty_iff.mp noObservation
    let state : State := Classical.choice (inferInstance : Nonempty State)
    have rowMass := targetStochastic.2 state
    simpa using rowMass
  have finiteKernelNonempty
      {Observation Action : Type u}
      [Fintype Observation] [Fintype Action]
      (actionNonempty : Nonempty Action) :
      Nonempty (FiniteMarkovKernel Observation Action) := by
    letI : Nonempty Action := actionNonempty
    refine ⟨⟨fun _ _ => (Fintype.card Action : Real)⁻¹, ?_⟩⟩
    constructor
    · intro observation action
      positivity
    · intro observation
      simp [Fintype.card_ne_zero]
  constructor
  · rintro ⟨simulator, rfl⟩ Action _ prior loss priorStochastic
    rcases isEmpty_or_nonempty Action with actionEmpty | actionNonempty
    · letI : IsEmpty Action := actionEmpty
      have sourceDecisionEmpty :
          IsEmpty (FiniteMarkovKernel SourceObservation Action) := by
        constructor
        intro decision
        let observation := Classical.choice sourceObservationNonempty
        have rowMass := decision.2.2 observation
        simpa using rowMass
      have targetDecisionEmpty :
          IsEmpty (FiniteMarkovKernel TargetObservation Action) := by
        constructor
        intro decision
        let observation := Classical.choice targetObservationNonempty
        have rowMass := decision.2.2 observation
        simpa using rowMass
      have sourceRangeEmpty :
          Set.range (fun decision : FiniteMarkovKernel SourceObservation Action =>
            finiteBayesCost prior loss source decision.1) = ∅ :=
        Set.range_eq_empty_iff.mpr sourceDecisionEmpty
      have targetRangeEmpty :
          Set.range (fun decision : FiniteMarkovKernel TargetObservation Action =>
            finiteBayesCost prior loss
              (fun state => channelOutput simulator.1 (source state)) decision.1) = ∅ :=
        Set.range_eq_empty_iff.mpr targetDecisionEmpty
      rw [sourceRangeEmpty, targetRangeEmpty]
    · letI : Nonempty Action := actionNonempty
      have costRangeBddBelow
          {Observation : Type u} [Fintype Observation]
          (experiment : State -> Observation -> Real)
          (experimentStochastic : IsRowStochastic experiment) :
          BddBelow (Set.range fun decision : FiniteMarkovKernel Observation Action =>
            finiteBayesCost prior loss experiment decision.1) := by
        refine ⟨∑ state, prior state * (-∑ action, |loss state action|), ?_⟩
        rintro _ ⟨decision, rfl⟩
        have outputStochastic :
            IsRowStochastic (fun state action =>
              channelOutput decision.1 (experiment state) action) := by
          constructor
          · intro state action
            unfold channelOutput
            exact Finset.sum_nonneg fun observation _ =>
              mul_nonneg (experimentStochastic.1 state observation)
                (decision.2.1 observation action)
          · intro state
            unfold channelOutput
            rw [Finset.sum_comm]
            calc
              (∑ observation, ∑ action,
                  experiment state observation * decision.1 observation action) =
                  ∑ observation,
                    experiment state observation *
                      ∑ action, decision.1 observation action := by
                        apply Finset.sum_congr rfl
                        intro observation _
                        rw [Finset.mul_sum]
              _ = ∑ observation, experiment state observation := by
                    apply Finset.sum_congr rfl
                    intro observation _
                    rw [decision.2.2 observation, mul_one]
              _ = 1 := experimentStochastic.2 state
        unfold finiteBayesCost
        apply Finset.sum_le_sum
        intro state _
        apply mul_le_mul_of_nonneg_left _ (priorStochastic.1 state)
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro action _
        have outputNonnegative := outputStochastic.1 state action
        have outputAtMostOne :
            channelOutput decision.1 (experiment state) action ≤ 1 := by
          exact (Finset.single_le_sum
            (fun candidate _ => outputStochastic.1 state candidate)
            (Finset.mem_univ action)).trans_eq (outputStochastic.2 state)
        have absProductLe :
            |channelOutput decision.1 (experiment state) action * loss state action| ≤
              |loss state action| := by
          rw [abs_mul, abs_of_nonneg outputNonnegative]
          exact mul_le_of_le_one_left (abs_nonneg _) outputAtMostOne
        exact (neg_le_neg absProductLe).trans (neg_abs_le _)
      have targetCostsNonempty :
          (Set.range fun decision : FiniteMarkovKernel TargetObservation Action =>
            finiteBayesCost prior loss
              (fun state => channelOutput simulator.1 (source state)) decision.1).Nonempty :=
        Set.range_nonempty_iff_nonempty.mpr (finiteKernelNonempty actionNonempty)
      apply csInf_le_csInf
        (costRangeBddBelow source sourceStochastic) targetCostsNonempty
      rintro _ ⟨decision, rfl⟩
      let transported : SourceObservation -> Action -> Real :=
        fun observation action =>
          channelOutput decision.1 (simulator.1 observation) action
      have transportedStochastic : IsRowStochastic transported := by
        constructor
        · intro observation action
          unfold transported channelOutput
          exact Finset.sum_nonneg fun targetObservation _ =>
            mul_nonneg (simulator.2.1 observation targetObservation)
              (decision.2.1 targetObservation action)
        · intro observation
          unfold transported channelOutput
          rw [Finset.sum_comm]
          calc
            (∑ targetObservation, ∑ action,
                simulator.1 observation targetObservation *
                  decision.1 targetObservation action) =
                ∑ targetObservation,
                  simulator.1 observation targetObservation *
                    ∑ action, decision.1 targetObservation action := by
                      apply Finset.sum_congr rfl
                      intro targetObservation _
                      rw [Finset.mul_sum]
            _ = ∑ targetObservation, simulator.1 observation targetObservation := by
                  apply Finset.sum_congr rfl
                  intro targetObservation _
                  rw [decision.2.2 targetObservation, mul_one]
            _ = 1 := simulator.2.2 observation
      let transportedKernel : FiniteMarkovKernel SourceObservation Action :=
        ⟨transported, transportedStochastic⟩
      refine ⟨transportedKernel, ?_⟩
      unfold finiteBayesCost
      apply Finset.sum_congr rfl
      intro state _
      congr 1
      apply Finset.sum_congr rfl
      intro action _
      congr 1
      have outputAssoc :
          channelOutput decision.1 (channelOutput simulator.1 (source state)) =
            channelOutput
              (fun observation action =>
                channelOutput decision.1 (simulator.1 observation) action)
              (source state) := by
        funext candidate
        simp only [channelOutput, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro observation _
        apply Finset.sum_congr rfl
        intro targetObservation _
        ring
      exact congrFun outputAssoc.symm action
  · intro riskDominance
    by_contra noSimulator
    let simulatorSet : Set (SourceObservation -> TargetObservation -> Real) :=
      Set.univ.pi (fun _ => stdSimplex Real TargetObservation)
    have simulatorMemIff
        (simulator : SourceObservation -> TargetObservation -> Real) :
        simulator ∈ simulatorSet ↔ IsRowStochastic simulator := by
      simp only [simulatorSet, Set.mem_pi, Set.mem_univ, true_implies,
        stdSimplex, IsRowStochastic]
      constructor
      · intro rows
        exact ⟨fun sourceObservation targetObservation =>
          (rows sourceObservation).1 targetObservation,
          fun sourceObservation => (rows sourceObservation).2⟩
      · rintro ⟨nonnegative, rowMass⟩ sourceObservation
        exact ⟨nonnegative sourceObservation, rowMass sourceObservation⟩
    let simulate :
        (SourceObservation -> TargetObservation -> Real) →ₗ[Real]
          (State -> TargetObservation -> Real) :=
      { toFun := fun simulator state =>
          channelOutput simulator (source state)
        map_add' := by
          intro left right
          funext state observation
          simp [channelOutput, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro scalar simulator
          funext state observation
          simp only [channelOutput, Real.ringHom_apply, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro sourceObservation _
          ring }
    let simulatedSet : Set (State -> TargetObservation -> Real) :=
      simulate '' simulatorSet
    have simulatorCompact : IsCompact simulatorSet := by
      dsimp only [simulatorSet]
      exact isCompact_univ_pi fun _ => isCompact_stdSimplex Real TargetObservation
    have simulatorConvex : Convex Real simulatorSet := by
      dsimp only [simulatorSet]
      exact convex_pi fun _ _ => convex_stdSimplex Real TargetObservation
    have simulatedCompact : IsCompact simulatedSet := by
      exact simulatorCompact.image simulate.continuous_of_finiteDimensional
    have simulatedConvex : Convex Real simulatedSet := by
      exact simulatorConvex.linear_image simulate
    have targetOutside : target ∉ simulatedSet := by
      rintro ⟨simulator, simulatorMem, simulatorTarget⟩
      apply noSimulator
      refine ⟨⟨simulator, (simulatorMemIff simulator).1 simulatorMem⟩, ?_⟩
      exact simulatorTarget.symm
    obtain ⟨witness, threshold, imageBelow, targetAbove⟩ :=
      geometric_hahn_banach_closed_point
        simulatedConvex simulatedCompact.isClosed targetOutside
    let coefficient : State -> TargetObservation -> Real := fun state observation =>
      witness (Pi.single state (Pi.single observation 1))
    have witnessExpansion (table : State -> TargetObservation -> Real) :
        witness table =
          ∑ state, ∑ observation,
            coefficient state observation * table state observation := by
      exact continuous_linear_expansion witness table
    let prior : State -> Real := fun _ => (Fintype.card State : Real)⁻¹
    have priorStochastic :
        (∀ state, 0 ≤ prior state) ∧ (∑ state, prior state) = 1 := by
      constructor
      · intro state
        positivity
      · simp [prior, Fintype.card_ne_zero]
    let constant : Real :=
      |threshold| + |witness target| +
        (∑ state, ∑ observation,
          |(Fintype.card State : Real) * coefficient state observation|) + 1
    let loss : State -> TargetObservation -> Real := fun state observation =>
      constant -
        (Fintype.card State : Real) * coefficient state observation
    have constantGreaterThreshold : threshold < constant := by
      dsimp only [constant]
      have thresholdLeAbs : threshold ≤ |threshold| := le_abs_self threshold
      have witnessAbsNonnegative : 0 ≤ |witness target| := abs_nonneg _
      have coefficientSumNonnegative :
          0 ≤ ∑ state, ∑ observation,
            |(Fintype.card State : Real) * coefficient state observation| := by
        positivity
      linarith
    have constantGreaterTarget : witness target < constant := by
      dsimp only [constant]
      have targetLeAbs : witness target ≤ |witness target| := le_abs_self _
      have thresholdAbsNonnegative : 0 ≤ |threshold| := abs_nonneg _
      have coefficientSumNonnegative :
          0 ≤ ∑ state, ∑ observation,
            |(Fintype.card State : Real) * coefficient state observation| := by
        positivity
      linarith
    have sourceCostLower
        (decision : FiniteMarkovKernel SourceObservation TargetObservation) :
        constant - threshold <
          finiteBayesCost prior loss source decision.1 := by
      have simulatedMem : simulate decision.1 ∈ simulatedSet := by
        exact ⟨decision.1, (simulatorMemIff decision.1).2 decision.2, rfl⟩
      have separated := imageBelow (simulate decision.1) simulatedMem
      rw [finite_bayes_cost_uniform_separator source decision.1
        sourceStochastic decision.2 coefficient constant]
      rw [← witnessExpansion]
      exact sub_lt_sub_left separated constant
    have sourceRiskLower :
        constant - threshold ≤
          sInf (Set.range fun decision :
            FiniteMarkovKernel SourceObservation TargetObservation =>
              finiteBayesCost prior loss source decision.1) := by
      apply le_csInf
        (Set.range_nonempty_iff_nonempty.mpr
          (finiteKernelNonempty targetObservationNonempty))
      rintro _ ⟨decision, rfl⟩
      exact (sourceCostLower decision).le
    let identityDecision : FiniteMarkovKernel TargetObservation TargetObservation :=
      ⟨deterministicPostprocess id, by
        constructor
        · intro observation action
          dsimp only [deterministicPostprocess]
          split <;> norm_num
        · intro observation
          dsimp only [deterministicPostprocess]
          exact Fintype.sum_ite_eq observation (fun _ => (1 : Real))⟩
    have identityOutput (state : State) :
        channelOutput identityDecision.1 (target state) = target state := by
      funext observation
      simp [identityDecision, deterministicPostprocess, channelOutput]
    have targetIdentityCost :
        finiteBayesCost prior loss target identityDecision.1 =
          constant - witness target := by
      rw [finite_bayes_cost_uniform_separator target identityDecision.1
        targetStochastic identityDecision.2 coefficient constant]
      rw [← witnessExpansion]
      congr 2
      funext state
      exact identityOutput state
    have lossNonnegative (state : State) (observation : TargetObservation) :
        0 ≤ loss state observation := by
      have innerLe :
          |(Fintype.card State : Real) * coefficient state observation| ≤
            ∑ candidate,
              |(Fintype.card State : Real) * coefficient state candidate| :=
        Finset.single_le_sum
          (f := fun candidate : TargetObservation =>
            |(Fintype.card State : Real) * coefficient state candidate|)
          (fun candidate _ => abs_nonneg _)
          (Finset.mem_univ observation)
      have outerLe :
          (∑ candidate,
              |(Fintype.card State : Real) * coefficient state candidate|) ≤
            ∑ candidateState, ∑ candidate,
              |(Fintype.card State : Real) *
                coefficient candidateState candidate| :=
        Finset.single_le_sum
          (f := fun candidateState : State => ∑ candidate,
            |(Fintype.card State : Real) * coefficient candidateState candidate|)
          (fun candidateState _ => Finset.sum_nonneg fun candidate _ => abs_nonneg _)
          (Finset.mem_univ state)
      have coefficientLe :
          (Fintype.card State : Real) * coefficient state observation ≤
            ∑ candidateState, ∑ candidate,
              |(Fintype.card State : Real) *
                coefficient candidateState candidate| :=
        (le_abs_self _).trans (innerLe.trans outerLe)
      dsimp only [loss, constant]
      linarith [abs_nonneg threshold, abs_nonneg (witness target)]
    have targetCostNonnegative
        (decision : FiniteMarkovKernel TargetObservation TargetObservation) :
        0 ≤ finiteBayesCost prior loss target decision.1 := by
      unfold finiteBayesCost
      apply Finset.sum_nonneg
      intro state _
      apply mul_nonneg (priorStochastic.1 state)
      apply Finset.sum_nonneg
      intro observation _
      apply mul_nonneg _ (lossNonnegative state observation)
      unfold channelOutput
      exact Finset.sum_nonneg fun targetObservation _ =>
        mul_nonneg (targetStochastic.1 state targetObservation)
          (decision.2.1 targetObservation observation)
    have targetCostsBddBelow :
        BddBelow (Set.range fun decision :
          FiniteMarkovKernel TargetObservation TargetObservation =>
            finiteBayesCost prior loss target decision.1) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨decision, rfl⟩
      exact targetCostNonnegative decision
    have targetRiskUpper :
        sInf (Set.range fun decision :
          FiniteMarkovKernel TargetObservation TargetObservation =>
            finiteBayesCost prior loss target decision.1) ≤
          constant - witness target := by
      calc
        sInf (Set.range fun decision :
            FiniteMarkovKernel TargetObservation TargetObservation =>
              finiteBayesCost prior loss target decision.1) ≤
            finiteBayesCost prior loss target identityDecision.1 :=
          csInf_le targetCostsBddBelow ⟨identityDecision, rfl⟩
        _ = constant - witness target := by
          rw [targetIdentityCost]
    have strictSeparatorRisk :
        constant - witness target < constant - threshold :=
      sub_lt_sub_left targetAbove constant
    have assumedOrder := riskDominance
      TargetObservation prior loss priorStochastic
    exact (not_lt_of_ge
      (sourceRiskLower.trans (assumedOrder.trans targetRiskUpper)))
        strictSeparatorRisk

#print axioms finite_bayes_risk_dominance_iff_postprocessing

end D5.S3.Estimation.DecisionRisk.FiniteBayesRiskDominanceCriterion
