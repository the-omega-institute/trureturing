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
     `channelOutput`, `finiteBayesCost`, and `finiteBayesRisk` are imported from
     their canonical D5 owners rather than redeclared.
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

private theorem channel_output_assoc
    {X Y Z : Type*} [Fintype X] [Fintype Y]
    (first : X -> Y -> Real) (second : Y -> Z -> Real)
    (mass : X -> Real) :
    channelOutput second (channelOutput first mass) =
      channelOutput (fun x z => channelOutput second (first x) z) mass := by
  classical
  funext z
  simp only [channelOutput, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem channel_compose_row_stochastic
    {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (first : X -> Y -> Real) (second : Y -> Z -> Real)
    (firstStochastic : IsRowStochastic first)
    (secondStochastic : IsRowStochastic second) :
    IsRowStochastic (fun x z => channelOutput second (first x) z) := by
  classical
  constructor
  · intro x z
    unfold channelOutput
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (firstStochastic.1 x y) (secondStochastic.1 y z)
  · intro x
    unfold channelOutput
    rw [Finset.sum_comm]
    calc
      (∑ y, ∑ z, first x y * second y z) =
          ∑ y, first x y * ∑ z, second y z := by
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.mul_sum]
      _ = ∑ y, first x y := by
            apply Finset.sum_congr rfl
            intro y _
            rw [secondStochastic.2 y, mul_one]
      _ = 1 := firstStochastic.2 x

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
  have outputStochastic := channel_compose_row_stochastic
    experiment decision experimentStochastic decisionStochastic
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
      finiteBayesRisk prior loss source ≤ finiteBayesRisk prior loss target := by
  classical
  constructor
  · rintro ⟨simulator, rfl⟩ Action _ prior loss _
    unfold finiteBayesRisk
    apply le_iInf
    intro decision
    let transported : SourceObservation -> Action -> Real :=
      fun observation action =>
        channelOutput decision.1 (simulator.1 observation) action
    have transportedStochastic : IsRowStochastic transported :=
      channel_compose_row_stochastic simulator.1 decision.1 simulator.2 decision.2
    let transportedKernel : FiniteMarkovKernel SourceObservation Action :=
      ⟨transported, transportedStochastic⟩
    calc
      (⨅ candidate : FiniteMarkovKernel SourceObservation Action,
          ENNReal.ofReal
            (finiteBayesCost prior loss source candidate.1)) ≤
          ENNReal.ofReal
            (finiteBayesCost prior loss source transportedKernel.1) :=
        iInf_le _ transportedKernel
      _ = ENNReal.ofReal
          (finiteBayesCost prior loss
            (fun state => channelOutput simulator.1 (source state)) decision.1) := by
        congr 1
        unfold finiteBayesCost
        apply Finset.sum_congr rfl
        intro state _
        congr 1
        apply Finset.sum_congr rfl
        intro action _
        congr 1
        exact congrFun
          (channel_output_assoc simulator.1 decision.1 (source state)).symm action
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
        ENNReal.ofReal (constant - threshold) ≤
          finiteBayesRisk prior loss source := by
      unfold finiteBayesRisk
      apply le_iInf
      intro decision
      exact ENNReal.ofReal_le_ofReal (sourceCostLower decision).le
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
    have targetRiskUpper :
        finiteBayesRisk prior loss target ≤
          ENNReal.ofReal (constant - witness target) := by
      unfold finiteBayesRisk
      calc
        (⨅ decision : FiniteMarkovKernel TargetObservation TargetObservation,
            ENNReal.ofReal (finiteBayesCost prior loss target decision.1)) ≤
            ENNReal.ofReal
              (finiteBayesCost prior loss target identityDecision.1) :=
          iInf_le _ identityDecision
        _ = ENNReal.ofReal (constant - witness target) := by
          rw [targetIdentityCost]
    have strictSeparatorRisk :
        ENNReal.ofReal (constant - witness target) <
          ENNReal.ofReal (constant - threshold) := by
      exact (ENNReal.ofReal_lt_ofReal_iff
        (sub_pos.mpr constantGreaterThreshold)).2
          (sub_lt_sub_left targetAbove constant)
    have assumedOrder := riskDominance
      TargetObservation prior loss priorStochastic
    exact (not_lt_of_ge
      (sourceRiskLower.trans (assumedOrder.trans targetRiskUpper)))
        strictSeparatorRisk

#print axioms finite_bayes_risk_dominance_iff_postprocessing

end D5.S3.Estimation.DecisionRisk.FiniteBayesRiskDominanceCriterion
