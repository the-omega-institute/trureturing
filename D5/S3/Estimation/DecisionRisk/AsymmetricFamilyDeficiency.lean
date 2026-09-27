/- GID: D5/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/AsymmetricFamilyDeficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Asymmetric-fibre deficiency is zero forward and positive backward. -/

import D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity

noncomputable section

open scoped BigOperators ENNReal Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- Along a fixed-`M`, fixed-`a` asymmetric-family fibre, increasing the second
label mass is an exact garbling through the displayed kernel, while the displayed
reverse kernel attains the stated positive deficiency in both states. -/
theorem asymmetric_family_deficiency
    (a M dOne dTwo : ℝ)
    (ha : 0 < 2 * a)
    (hM : M < 1)
    (hadOne : a ≤ dOne)
    (hdOneTwo : dOne < dTwo)
    (hdTwo : dTwo < M - a) :
    let D := 1 - M
    let L := M - a
    let QOne := asymmetricExperiment a dOne (L - dOne)
    let QTwo := asymmetricExperiment a dTwo (L - dTwo)
    let gamma := D * (dTwo - dOne) / (2 * dTwo + D)
    let h := 2 * (dTwo - dOne) / (2 * dTwo + D)
    finiteDeficiency QTwo QOne = 0 ∧
      finiteDeficiency QOne QTwo = ENNReal.ofReal gamma ∧
      0 < gamma ∧
      0 < (dTwo - dOne) / (L - dOne) ∧
      (dTwo - dOne) / (L - dOne) < 1 ∧
      0 < h ∧
      h < 1 ∧
      (∃ K : FiniteMarkovKernel (Fin 3) (Fin 3),
        K.1 = !![1 - (dTwo - dOne) / (L - dOne), 0, (dTwo - dOne) / (L - dOne);
                 0, 1, 0;
                 0, 0, 1] ∧
        ∀ state : Fin 2, channelOutput K.1 (QOne state) = QTwo state) ∧
      ∃ reverseKernel : FiniteMarkovKernel (Fin 3) (Fin 3),
        reverseKernel.1 = !![1, 0, 0;
                             0, 1, 0;
                             h, 0, 1 - h] ∧
        (∀ state : Fin 2,
          totalVariation (QOne state)
            (channelOutput reverseKernel.1 (QTwo state)) = gamma) ∧
        uniformSimulationError QOne QTwo reverseKernel = gamma := by
  let D := 1 - M
  let L := M - a
  let delta := dTwo - dOne
  let bOne := L - dOne
  let bTwo := L - dTwo
  let QOne := asymmetricExperiment a dOne bOne
  let QTwo := asymmetricExperiment a dTwo bTwo
  let forwardProbability := delta / bOne
  let gamma := D * delta / (2 * dTwo + D)
  let h := 2 * delta / (2 * dTwo + D)
  change finiteDeficiency QTwo QOne = 0 ∧
    finiteDeficiency QOne QTwo = ENNReal.ofReal gamma ∧
    0 < gamma ∧
    0 < forwardProbability ∧
    forwardProbability < 1 ∧
    0 < h ∧
    h < 1 ∧
    (∃ K : FiniteMarkovKernel (Fin 3) (Fin 3),
      K.1 = !![1 - forwardProbability, 0, forwardProbability;
               0, 1, 0;
               0, 0, 1] ∧
      ∀ state : Fin 2, channelOutput K.1 (QOne state) = QTwo state) ∧
    ∃ reverseKernel : FiniteMarkovKernel (Fin 3) (Fin 3),
      reverseKernel.1 = !![1, 0, 0;
                           0, 1, 0;
                           h, 0, 1 - h] ∧
      (∀ state : Fin 2,
        totalVariation (QOne state)
          (channelOutput reverseKernel.1 (QTwo state)) = gamma) ∧
      uniformSimulationError QOne QTwo reverseKernel = gamma
  have haM : 2 * a < M := by linarith
  have haPos : 0 < a := pos_of_mul_pos_right ha (by norm_num)
  have hMPos : 0 < M := ha.trans haM
  have hD : 0 < D := by
    dsimp [D]
    exact sub_pos.mpr hM
  have hdOnePos : 0 < dOne := lt_of_lt_of_le haPos hadOne
  have hdTwoPos : 0 < dTwo := hdOnePos.trans hdOneTwo
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact sub_pos.mpr hdOneTwo
  have hbOne : 0 < bOne := by
    dsimp [bOne, L]
    exact sub_pos.mpr (hdOneTwo.trans hdTwo)
  have hbTwo : 0 < bTwo := by
    dsimp [bTwo, L]
    exact sub_pos.mpr hdTwo
  have hden : 0 < 2 * dTwo + D :=
    add_pos (mul_pos (by norm_num) hdTwoPos) hD
  have hgamma : 0 < gamma := div_pos (mul_pos hD hdelta) hden
  have hExperimentStochastic : ∀ d b : ℝ,
      0 < d → 0 < b → b + a + d = M →
      IsRowStochastic (asymmetricExperiment a d b) := by
    intro d b hd hb hsum
    constructor
    · intro state output
      fin_cases state <;> fin_cases output <;>
        simp [asymmetricExperiment] <;> linarith
    · intro state
      fin_cases state <;>
        simp [asymmetricExperiment, Fin.sum_univ_succ] <;> linarith
  have hsumOne : bOne + a + dOne = M := by
    dsimp [bOne, L]
    ring
  have hsumTwo : bTwo + a + dTwo = M := by
    dsimp [bTwo, L]
    ring
  have hQOneStochastic : IsRowStochastic QOne := by
    apply hExperimentStochastic dOne bOne hdOnePos hbOne
    exact hsumOne
  have hQTwoStochastic : IsRowStochastic QTwo := by
    apply hExperimentStochastic dTwo bTwo hdTwoPos hbTwo
    exact hsumTwo
  have hForwardProbabilityPos : 0 < forwardProbability :=
    div_pos hdelta hbOne
  have hForwardProbabilityLt : forwardProbability < 1 := by
    rw [div_lt_one hbOne]
    dsimp [delta, bOne, L]
    linarith
  let forwardKernel : FiniteMarkovKernel (Fin 3) (Fin 3) :=
    ⟨!![1 - forwardProbability, 0, forwardProbability;
        0, 1, 0;
        0, 0, 1], by
      constructor
      · intro source target
        fin_cases source <;> fin_cases target <;>
          simp <;> linarith
      · intro source
        fin_cases source <;> simp [Fin.sum_univ_succ]⟩
  have hForwardIdentity : ∀ state : Fin 2,
      channelOutput forwardKernel.1 (QOne state) = QTwo state := by
    intro state
    funext output
    fin_cases state <;> fin_cases output <;>
      simp [forwardKernel, forwardProbability, QOne, QTwo,
        asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    all_goals
      try field_simp [ne_of_gt hbOne]
      dsimp [bOne, bTwo, delta, L]
      ring
  have hForwardError : uniformSimulationError QTwo QOne forwardKernel = 0 := by
    have htv : ∀ state : Fin 2,
        totalVariation (QTwo state)
          (channelOutput forwardKernel.1 (QOne state)) = 0 := by
      intro state
      exact (total_variation_eq_zero_iff _ _).2 (hForwardIdentity state).symm
    unfold uniformSimulationError
    simp [htv]
  have hForwardDeficiency : finiteDeficiency QTwo QOne = 0 := by
    apply le_antisymm
    · unfold finiteDeficiency
      exact (iInf_le _ forwardKernel).trans_eq (by simp [hForwardError])
    · exact bot_le
  have hReverseProbabilityPos : 0 < h := by
    exact div_pos (mul_pos (by norm_num) hdelta) hden
  have hReverseProbabilityLt : h < 1 := by
    rw [div_lt_one hden]
    dsimp [h, delta, D]
    linarith
  let reverseKernel : FiniteMarkovKernel (Fin 3) (Fin 3) :=
    ⟨!![1, 0, 0;
        0, 1, 0;
        h, 0, 1 - h], by
      constructor
      · intro source target
        fin_cases source <;> fin_cases target <;>
          simp <;> linarith
      · intro source
        fin_cases source <;> simp [Fin.sum_univ_succ]⟩
  have hReverseDifference00 : QOne 0 0 -
      channelOutput reverseKernel.1 (QTwo 0) 0 = gamma := by
    simp [reverseKernel, h, QOne, QTwo, gamma,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    field_simp [ne_of_gt hden]
    dsimp [bOne, bTwo, delta, L, D]
    ring
  have hReverseDifference01 : QOne 0 1 -
      channelOutput reverseKernel.1 (QTwo 0) 1 = 0 := by
    simp [reverseKernel, QOne, QTwo, bOne, bTwo, L,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    ring
  have hReverseDifference02 : QOne 0 2 -
      channelOutput reverseKernel.1 (QTwo 0) 2 = -gamma := by
    simp [reverseKernel, h, QOne, QTwo, gamma,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    field_simp [ne_of_gt hden]
    dsimp [bOne, bTwo, delta, L, D]
    ring
  have hReverseDifference10 : QOne 1 0 -
      channelOutput reverseKernel.1 (QTwo 1) 0 = -gamma := by
    simp [reverseKernel, h, QOne, QTwo, gamma,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    field_simp [ne_of_gt hden]
    dsimp [bOne, bTwo, delta, L, D]
    ring
  have hReverseDifference11 : QOne 1 1 -
      channelOutput reverseKernel.1 (QTwo 1) 1 = 0 := by
    simp [reverseKernel, QOne, QTwo, bOne, bTwo, L,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
  have hReverseDifference12 : QOne 1 2 -
      channelOutput reverseKernel.1 (QTwo 1) 2 = gamma := by
    simp [reverseKernel, h, QOne, QTwo, gamma,
      asymmetricExperiment, channelOutput, Fin.sum_univ_succ]
    field_simp [ne_of_gt hden]
    dsimp [bOne, bTwo, delta, L, D]
    ring
  have hReverseTv : ∀ state : Fin 2,
      totalVariation (QOne state)
        (channelOutput reverseKernel.1 (QTwo state)) = gamma := by
    intro state
    fin_cases state
    · simp [totalVariation, Fin.sum_univ_succ, hReverseDifference00,
        hReverseDifference01, hReverseDifference02, abs_of_pos hgamma,
        abs_of_neg (neg_lt_zero.mpr hgamma)]
      ring
    · simp [totalVariation, Fin.sum_univ_succ, hReverseDifference10,
        hReverseDifference11, hReverseDifference12, abs_of_pos hgamma,
        abs_of_neg (neg_lt_zero.mpr hgamma)]
      ring
  have hReverseError : uniformSimulationError QOne QTwo reverseKernel = gamma := by
    unfold uniformSimulationError
    simp [hReverseTv]
  have hReverseUpper : finiteDeficiency QOne QTwo ≤ ENNReal.ofReal gamma := by
    unfold finiteDeficiency
    exact (iInf_le _ reverseKernel).trans_eq (by rw [hReverseError])
  let tTwo := (dTwo + D) / (2 * dTwo + D)
  have htTwoHalf : 1 / 2 < tTwo := by
    dsimp [tTwo]
    rw [lt_div_iff₀ hden]
    nlinarith
  have htTwoOne : tTwo < 1 := by
    dsimp [tTwo]
    rw [div_lt_iff₀ hden]
    nlinarith
  have htTwoRange : tTwo ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htTwoHalf.le.trans' (by norm_num), htTwoOne.le⟩
  let prior : Fin 2 → ℝ := ![tTwo, 1 - tTwo]
  let loss : Fin 2 → Fin 2 → ℝ :=
    fun state action => if state = action then 0 else 1
  have hPriorStochastic :
      (∀ state, 0 ≤ prior state) ∧ (∑ state, prior state) = 1 := by
    constructor
    · intro state
      fin_cases state <;> simp [prior] <;> linarith
    · simp [prior, Fin.sum_univ_succ]
  have hLossBounded : ∀ state action,
      0 ≤ loss state action ∧ loss state action ≤ 1 := by
    intro state action
    simp only [loss]
    split <;> norm_num
  have hRiskBridge : ∀ d b : ℝ,
      finiteBayesRisk prior loss (asymmetricExperiment a d b) =
        ENNReal.ofReal (asymmetricBayesRisk a d b tTwo) := by
    intro d b
    unfold finiteBayesRisk asymmetricBayesRisk
    dsimp [prior, loss]
    let defaultDecision : FiniteMarkovKernel (Fin 3) (Fin 2) :=
      ⟨!![1, 0; 1, 0; 1, 0], by
        constructor
        · intro output action
          fin_cases output <;> fin_cases action <;> norm_num
        · intro output
          fin_cases output <;> simp [Fin.sum_univ_succ]⟩
    let decisionNonempty : Nonempty (FiniteMarkovKernel (Fin 3) (Fin 2)) :=
      ⟨defaultDecision⟩
    change (⨅ decision : FiniteMarkovKernel (Fin 3) (Fin 2),
      ENNReal.ofReal
        (finiteBayesCost ![tTwo, 1 - tTwo]
          (fun state action : Fin 2 => if state = action then 0 else 1)
          (asymmetricExperiment a d b) decision.1)) =
      ENNReal.ofReal
        (⨅ decision : FiniteMarkovKernel (Fin 3) (Fin 2),
          finiteBayesCost ![tTwo, 1 - tTwo]
            (fun state action : Fin 2 => if state = action then 0 else 1)
            (asymmetricExperiment a d b) decision.1)
    exact (@ENNReal.ofReal_iInf
      (FiniteMarkovKernel (Fin 3) (Fin 2)) decisionNonempty _).symm
  have hRiskFormulaTwo :=
    (asymmetric_family_risk_and_injective_queries
      a dTwo bTwo tTwo a M tTwo).1
      ⟨haPos, hadOne.trans hdOneTwo.le, hbTwo, by
        dsimp [bTwo, L]
        linarith, htTwoRange⟩
  have hRiskTwo : asymmetricBayesRisk a dTwo bTwo tTwo = 1 - tTwo := by
    have htPlusTwo :
        (dTwo + (1 - (bTwo + a + dTwo))) /
          (2 * dTwo + (1 - (bTwo + a + dTwo))) = tTwo := by
      rw [hsumTwo]
    apply hRiskFormulaTwo.2.2.2.2
    rw [htPlusTwo]
    exact ⟨le_rfl, htTwoOne.le⟩
  let tOne := (dOne + D) / (2 * dOne + D)
  have hdenOne : 0 < 2 * dOne + D :=
    add_pos (mul_pos (by norm_num) hdOnePos) hD
  have htTwoLeOne : tTwo ≤ tOne := by
    dsimp [tTwo, tOne]
    rw [div_le_div_iff₀ hden hdenOne]
    nlinarith
  have hRiskFormulaOne :=
    (asymmetric_family_risk_and_injective_queries
      a dOne bOne tTwo a M tTwo).1
      ⟨haPos, hadOne, hbOne, by
        dsimp [bOne, L]
        linarith, htTwoRange⟩
  have hRiskOne : asymmetricBayesRisk a dOne bOne tTwo =
      M * (1 - tTwo) + (2 * tTwo - 1) * dOne := by
    have htPlusOne :
        (dOne + (1 - (bOne + a + dOne))) /
          (2 * dOne + (1 - (bOne + a + dOne))) = tOne := by
      rw [hsumOne]
    have hrisk := hRiskFormulaOne.2.2.2.1 (by
      rw [htPlusOne]
      exact ⟨htTwoHalf.le, htTwoLeOne⟩)
    rw [hsumOne] at hrisk
    exact hrisk
  have hRiskGap : asymmetricBayesRisk a dTwo bTwo tTwo =
      asymmetricBayesRisk a dOne bOne tTwo + gamma := by
    rw [hRiskTwo, hRiskOne]
    dsimp [tTwo, gamma, delta]
    field_simp [ne_of_gt hden]
    ring
  have hRiskOneNonnegative :
      0 ≤ asymmetricBayesRisk a dOne bOne tTwo := by
    rw [hRiskOne]
    have hOneMinus : 0 ≤ 1 - tTwo := sub_nonneg.mpr htTwoOne.le
    have hSlope : 0 ≤ 2 * tTwo - 1 := by linarith
    exact add_nonneg (mul_nonneg hMPos.le hOneMinus)
      (mul_nonneg hSlope hdOnePos.le)
  have hRiskTransfer := deficiency_risk_bound prior loss QTwo QOne
    hPriorStochastic hQTwoStochastic hQOneStochastic hLossBounded
  have hReverseLower : ENNReal.ofReal gamma ≤ finiteDeficiency QOne QTwo := by
    rw [hRiskBridge dTwo bTwo, hRiskBridge dOne bOne, hRiskGap,
      ENNReal.ofReal_add hRiskOneNonnegative hgamma.le] at hRiskTransfer
    exact ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top hRiskTransfer
  refine ⟨hForwardDeficiency, le_antisymm hReverseUpper hReverseLower, hgamma,
    hForwardProbabilityPos, hForwardProbabilityLt,
    hReverseProbabilityPos, hReverseProbabilityLt, ?_, ?_⟩
  · exact ⟨forwardKernel, rfl, hForwardIdentity⟩
  · exact ⟨reverseKernel, rfl, hReverseTv, hReverseError⟩

#print axioms asymmetric_family_deficiency

end D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
