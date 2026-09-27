/- GID: D5/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/AsymmetricFamilyRiskInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Asymmetric Bayes risks are explicit and their injective queries are classified. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

noncomputable section

open Set
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

/-- The two rows of the asymmetric three-output experiment. -/
def asymmetricExperiment (a d b : ℝ) : Fin 2 → Fin 3 → ℝ :=
  !![b, a + (1 - (b + a + d)), d;
     b, a, d + (1 - (b + a + d))]

/-- The optimal zero-one Bayes risk of the asymmetric experiment. -/
def asymmetricBayesRisk (a d b pi : ℝ) : ℝ :=
  sInf (Set.range fun decision : FiniteMarkovKernel (Fin 3) (Fin 2) =>
    finiteBayesCost ![pi, 1 - pi]
      (fun state action : Fin 2 => if state = action then 0 else 1)
      (asymmetricExperiment a d b) decision.1)

/-- The Bayes-risk query along the fixed-`M`, fixed-`a` parameter fiber. -/
def asymmetricFiberRisk (M a pi d : ℝ) : ℝ :=
  asymmetricBayesRisk a d (M - a - d) pi

/-- The asymmetric family has the stated four-piece Bayes risk, and a risk query is injective
on a fixed-curve fiber exactly up to the saturation prior. -/
theorem asymmetric_family_risk_and_injective_queries
    (aOne dOne bOne piOne aTwo MTwo piTwo : ℝ) :
    ((0 < aOne ∧ aOne ≤ dOne ∧ 0 < bOne ∧ bOne + aOne + dOne < 1 ∧
        piOne ∈ Set.Icc (0 : ℝ) 1) →
      let M := bOne + aOne + dOne
      let D := 1 - M
      let tMinus := aOne / (2 * aOne + D)
      let tPlus := (dOne + D) / (2 * dOne + D)
      (0 < tMinus ∧ tMinus < 1 / 2 ∧ 1 / 2 < tPlus ∧ tPlus < 1) ∧
      (piOne ∈ Set.Icc 0 tMinus →
        asymmetricBayesRisk aOne dOne bOne piOne = piOne) ∧
      (piOne ∈ Set.Icc tMinus (1 / 2) →
        asymmetricBayesRisk aOne dOne bOne piOne =
          aOne + piOne * (M - 2 * aOne)) ∧
      (piOne ∈ Set.Icc (1 / 2) tPlus →
        asymmetricBayesRisk aOne dOne bOne piOne =
          M * (1 - piOne) + (2 * piOne - 1) * dOne) ∧
      (piOne ∈ Set.Icc tPlus 1 →
        asymmetricBayesRisk aOne dOne bOne piOne = 1 - piOne)) ∧
    ((0 < 2 * aTwo ∧ 2 * aTwo < MTwo ∧ MTwo < 1 ∧
        1 / 2 < piTwo ∧ piTwo ≤ 1) →
      let D := 1 - MTwo
      let L := MTwo - aTwo
      let U := 2 * L + D
      let s := 2 * piTwo - 1
      let c := MTwo * (1 - piTwo)
      let t := D * (1 - s) / (2 * s)
      (∀ d ∈ Set.Ico aTwo L,
        asymmetricFiberRisk MTwo aTwo piTwo d = c + s * min d t) ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) ↔
        piTwo ≤ (L + D) / (2 * L + D)) ∧
      (L + D) / (2 * L + D) = (1 + D / U) / 2 ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) →
        s ≤ D / U) ∧
      Set.InjOn
        (asymmetricFiberRisk MTwo aTwo ((L + D) / (2 * L + D)))
        (Set.Ico aTwo L) ∧
      2 * ((L + D) / (2 * L + D)) - 1 = D / U) := by
  have optimalRisk : ∀ (a d b pi : ℝ),
      asymmetricBayesRisk a d b pi =
        ∑ output : Fin 3,
          min (pi * asymmetricExperiment a d b 0 output)
            ((1 - pi) * asymmetricExperiment a d b 1 output) := by
    intro a d b pi
    let lower := ∑ output : Fin 3,
      min (pi * asymmetricExperiment a d b 0 output)
        ((1 - pi) * asymmetricExperiment a d b 1 output)
    have costFormula (decision : FiniteMarkovKernel (Fin 3) (Fin 2)) :
        finiteBayesCost ![pi, 1 - pi]
            (fun state action : Fin 2 => if state = action then 0 else 1)
            (asymmetricExperiment a d b) decision.1 =
          ∑ output : Fin 3,
            (pi * asymmetricExperiment a d b 0 output * decision.1 output 1 +
              (1 - pi) * asymmetricExperiment a d b 1 output * decision.1 output 0) := by
      simp [finiteBayesCost, channelOutput, Fin.sum_univ_succ]
      ring
    have lowerBound (decision : FiniteMarkovKernel (Fin 3) (Fin 2)) :
        lower ≤ finiteBayesCost ![pi, 1 - pi]
          (fun state action : Fin 2 => if state = action then 0 else 1)
          (asymmetricExperiment a d b) decision.1 := by
      rw [costFormula]
      apply Finset.sum_le_sum
      intro output _
      have hrow := decision.2.2 output
      have hzero := decision.2.1 output 0
      have hone := decision.2.1 output 1
      have hleft := mul_le_mul_of_nonneg_right
        (min_le_left
          (pi * asymmetricExperiment a d b 0 output)
          ((1 - pi) * asymmetricExperiment a d b 1 output)) hone
      have hright := mul_le_mul_of_nonneg_right
        (min_le_right
          (pi * asymmetricExperiment a d b 0 output)
          ((1 - pi) * asymmetricExperiment a d b 1 output)) hzero
      have hrow' : decision.1 output 0 + decision.1 output 1 = 1 := by
        simpa only [Fin.sum_univ_two] using hrow
      calc
        min (pi * asymmetricExperiment a d b 0 output)
            ((1 - pi) * asymmetricExperiment a d b 1 output) =
            min (pi * asymmetricExperiment a d b 0 output)
              ((1 - pi) * asymmetricExperiment a d b 1 output) *
              (decision.1 output 0 + decision.1 output 1) := by rw [hrow', mul_one]
        _ = min (pi * asymmetricExperiment a d b 0 output)
                ((1 - pi) * asymmetricExperiment a d b 1 output) *
              decision.1 output 1 +
            min (pi * asymmetricExperiment a d b 0 output)
                ((1 - pi) * asymmetricExperiment a d b 1 output) *
              decision.1 output 0 := by ring
        _ ≤ pi * asymmetricExperiment a d b 0 output * decision.1 output 1 +
            (1 - pi) * asymmetricExperiment a d b 1 output *
              decision.1 output 0 := add_le_add hleft hright
    let chosen : Fin 3 → Fin 2 := fun output =>
      if pi * asymmetricExperiment a d b 0 output ≤
          (1 - pi) * asymmetricExperiment a d b 1 output then 1 else 0
    let attainingDecision : FiniteMarkovKernel (Fin 3) (Fin 2) :=
      ⟨fun output action => if action = chosen output then 1 else 0, by
        constructor
        · intro output action
          positivity
        · intro output
          simp⟩
    have attainingCost :
        finiteBayesCost ![pi, 1 - pi]
            (fun state action : Fin 2 => if state = action then 0 else 1)
            (asymmetricExperiment a d b) attainingDecision.1 = lower := by
      rw [costFormula]
      apply Finset.sum_congr rfl
      intro output _
      by_cases hchoice : pi * asymmetricExperiment a d b 0 output ≤
          (1 - pi) * asymmetricExperiment a d b 1 output
      · simp [attainingDecision, chosen, hchoice]
      · have hreverse : (1 - pi) * asymmetricExperiment a d b 1 output ≤
            pi * asymmetricExperiment a d b 0 output := le_of_not_ge hchoice
        simp [attainingDecision, chosen, hchoice, min_eq_right hreverse]
    unfold asymmetricBayesRisk
    apply IsLeast.csInf_eq
    refine ⟨⟨attainingDecision, attainingCost⟩, ?_⟩
    rintro value ⟨decision, rfl⟩
    exact lowerBound decision
  have familyRisk : ∀ (a d b pi : ℝ),
      0 < a → a ≤ d → 0 < b → b + a + d < 1 →
      pi ∈ Set.Icc (0 : ℝ) 1 →
      let M := b + a + d
      let D := 1 - M
      let tMinus := a / (2 * a + D)
      let tPlus := (d + D) / (2 * d + D)
      (0 < tMinus ∧ tMinus < 1 / 2 ∧ 1 / 2 < tPlus ∧ tPlus < 1) ∧
      (pi ∈ Set.Icc 0 tMinus → asymmetricBayesRisk a d b pi = pi) ∧
      (pi ∈ Set.Icc tMinus (1 / 2) →
        asymmetricBayesRisk a d b pi = a + pi * (M - 2 * a)) ∧
      (pi ∈ Set.Icc (1 / 2) tPlus →
        asymmetricBayesRisk a d b pi =
          M * (1 - pi) + (2 * pi - 1) * d) ∧
      (pi ∈ Set.Icc tPlus 1 → asymmetricBayesRisk a d b pi = 1 - pi) := by
    intro a d b pi ha had hb hM hpi
    dsimp only
    have hd : 0 < d := lt_of_lt_of_le ha had
    have hD : 0 < 1 - (b + a + d) := by linarith
    have hdenMinus : 0 < 2 * a + (1 - (b + a + d)) := by linarith
    have hdenPlus : 0 < 2 * d + (1 - (b + a + d)) := by linarith
    have hminB : min (pi * b) ((1 - pi) * b) = b * min pi (1 - pi) := by
      rw [← min_mul_of_nonneg pi (1 - pi) hb.le, mul_comm]
    have hRisk : asymmetricBayesRisk a d b pi =
        b * min pi (1 - pi) +
          min (pi * (a + (1 - (b + a + d)))) ((1 - pi) * a) +
          min (pi * d) ((1 - pi) * (d + (1 - (b + a + d)))) := by
      rw [optimalRisk a d b pi]
      simp only [asymmetricExperiment, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_const, Finset.card_singleton, one_smul]
      rw [hminB]
      ring
    have htMinusPos : 0 < a / (2 * a + (1 - (b + a + d))) :=
      div_pos ha hdenMinus
    have htMinusHalf : a / (2 * a + (1 - (b + a + d))) < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ hdenMinus]
      nlinarith
    have htPlusHalf : (1 / 2 : ℝ) <
        (d + (1 - (b + a + d))) / (2 * d + (1 - (b + a + d))) := by
      rw [lt_div_iff₀ hdenPlus]
      nlinarith
    have htPlusOne :
        (d + (1 - (b + a + d))) / (2 * d + (1 - (b + a + d))) < 1 := by
      rw [div_lt_iff₀ hdenPlus]
      nlinarith
    refine ⟨⟨htMinusPos, htMinusHalf, htPlusHalf, htPlusOne⟩, ?_, ?_, ?_, ?_⟩
    · intro hinterval
      have hcommon : pi ≤ 1 - pi := by
        exact (hinterval.2.trans_lt htMinusHalf).le |> fun h => by nlinarith
      have hminusScaled : pi * (2 * a + (1 - (b + a + d))) ≤ a :=
        (le_div_iff₀ hdenMinus).mp hinterval.2
      have hminus : pi * (a + (1 - (b + a + d))) ≤ (1 - pi) * a := by
        nlinarith
      have hplus : pi * d ≤ (1 - pi) * (d + (1 - (b + a + d))) := by
        have hhalf : pi ≤ 1 / 2 := (hinterval.2.trans_lt htMinusHalf).le
        nlinarith [mul_nonneg hpi.1 hd.le,
          mul_nonneg (sub_nonneg.mpr hpi.2) hD.le]
      rw [hRisk, min_eq_left hcommon, min_eq_left hminus, min_eq_left hplus]
      ring
    · intro hinterval
      have hcommon : pi ≤ 1 - pi := by nlinarith [hinterval.2]
      have hminusScaled : a ≤ pi * (2 * a + (1 - (b + a + d))) :=
        (div_le_iff₀ hdenMinus).mp hinterval.1
      have hminus : (1 - pi) * a ≤ pi * (a + (1 - (b + a + d))) := by
        nlinarith
      have hplus : pi * d ≤ (1 - pi) * (d + (1 - (b + a + d))) := by
        nlinarith [hD, hd]
      rw [hRisk, min_eq_left hcommon, min_eq_right hminus, min_eq_left hplus]
      ring
    · intro hinterval
      have hcommon : 1 - pi ≤ pi := by nlinarith [hinterval.1]
      have hminus : (1 - pi) * a ≤ pi * (a + (1 - (b + a + d))) := by
        nlinarith [hD, ha]
      have hplusScaled :
          pi * (2 * d + (1 - (b + a + d))) ≤ d + (1 - (b + a + d)) :=
        (le_div_iff₀ hdenPlus).mp hinterval.2
      have hplus : pi * d ≤ (1 - pi) * (d + (1 - (b + a + d))) := by
        nlinarith
      rw [hRisk, min_eq_right hcommon, min_eq_right hminus, min_eq_left hplus]
      ring
    · intro hinterval
      have hcommon : 1 - pi ≤ pi := by
        have := htPlusHalf.trans_le hinterval.1
        nlinarith
      have hminus : (1 - pi) * a ≤ pi * (a + (1 - (b + a + d))) := by
        nlinarith [hD, ha]
      have hplusScaled : d + (1 - (b + a + d)) ≤
          pi * (2 * d + (1 - (b + a + d))) :=
        (div_le_iff₀ hdenPlus).mp hinterval.1
      have hplus : (1 - pi) * (d + (1 - (b + a + d))) ≤ pi * d := by
        nlinarith
      rw [hRisk, min_eq_right hcommon, min_eq_right hminus, min_eq_right hplus]
      ring
  constructor
  · intro h
    exact familyRisk aOne dOne bOne piOne h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  · intro h
    rcases h with ⟨haTwo, hTwoA, hMOne, hPiHalf, hPiOne⟩
    let D := 1 - MTwo
    let L := MTwo - aTwo
    let U := 2 * L + D
    let s := 2 * piTwo - 1
    let c := MTwo * (1 - piTwo)
    let t := D * (1 - s) / (2 * s)
    change
      (∀ d ∈ Set.Ico aTwo L,
        asymmetricFiberRisk MTwo aTwo piTwo d = c + s * min d t) ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) ↔
        piTwo ≤ (L + D) / (2 * L + D)) ∧
      (L + D) / (2 * L + D) = (1 + D / U) / 2 ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) →
        s ≤ D / U) ∧
      Set.InjOn
        (asymmetricFiberRisk MTwo aTwo ((L + D) / (2 * L + D)))
        (Set.Ico aTwo L) ∧
      2 * ((L + D) / (2 * L + D)) - 1 = D / U
    have ha : 0 < aTwo := by nlinarith
    have hD : 0 < D := by dsimp [D]; linarith
    have haL : aTwo < L := by dsimp [L]; linarith
    have hU : 0 < U := by dsimp [U]; nlinarith
    have truncatedRisk : ∀ (p : ℝ), 1 / 2 < p → p ≤ 1 →
        ∀ d ∈ Set.Ico aTwo L,
          asymmetricFiberRisk MTwo aTwo p d =
            MTwo * (1 - p) + (2 * p - 1) *
              min d (D * (1 - (2 * p - 1)) / (2 * (2 * p - 1))) := by
      intro p hpHalf hpOne d hdIco
      have hpRange : p ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith, hpOne⟩
      have hb : 0 < MTwo - aTwo - d := sub_pos.mpr hdIco.2
      have hsum : (MTwo - aTwo - d) + aTwo + d = MTwo := by ring
      have hfamily := familyRisk aTwo d (MTwo - aTwo - d) p ha hdIco.1 hb
        (by nlinarith [hMOne]) hpRange
      simp only [hsum] at hfamily
      have hsp : 0 < 2 * p - 1 := by nlinarith
      have hden : 0 < 2 * d + D := by
        dsimp [D]
        nlinarith [hdIco.1]
      let tp := D * (1 - (2 * p - 1)) / (2 * (2 * p - 1))
      by_cases hdt : d ≤ tp
      · have hscaled : p * (2 * d + D) ≤ d + D := by
          have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (2 * p - 1))).mp hdt
          dsimp [tp, D] at hmul ⊢
          nlinarith
        have hpThreshold : p ≤ (d + D) / (2 * d + D) :=
          (le_div_iff₀ hden).2 hscaled
        have hpPiece : p ∈ Set.Icc (1 / 2) ((d + D) / (2 * d + D)) :=
          ⟨hpHalf.le, hpThreshold⟩
        have hpRisk := hfamily.2.2.2.1 hpPiece
        rw [asymmetricFiberRisk, hpRisk, min_eq_left hdt]
      · have htd : tp ≤ d := le_of_not_ge hdt
        have hscaled : d + D ≤ p * (2 * d + D) := by
          have hmul := (div_le_iff₀ (by positivity : 0 < 2 * (2 * p - 1))).mp htd
          dsimp [tp, D] at hmul ⊢
          nlinarith
        have hpThreshold : (d + D) / (2 * d + D) ≤ p :=
          (div_le_iff₀ hden).2 hscaled
        have hpPiece : p ∈ Set.Icc ((d + D) / (2 * d + D)) 1 :=
          ⟨hpThreshold, hpOne⟩
        have hpRisk := hfamily.2.2.2.2 hpPiece
        have htruncate : (2 * p - 1) * tp = D * (1 - p) := by
          dsimp [tp]
          field_simp
          ring
        rw [asymmetricFiberRisk, hpRisk, min_eq_right htd]
        dsimp [D] at htruncate ⊢
        nlinarith
    have htruncated := truncatedRisk piTwo hPiHalf hPiOne
    have hFiber : ∀ d ∈ Set.Ico aTwo L,
        asymmetricFiberRisk MTwo aTwo piTwo d = c + s * min d t := by
      intro d hd
      simpa [c, s, t] using htruncated d hd
    have hdenStar : 0 < 2 * L + D := by simpa [U] using hU
    have injectiveClassification : ∀ (p : ℝ), 1 / 2 < p → p ≤ 1 →
        (Set.InjOn (asymmetricFiberRisk MTwo aTwo p) (Set.Ico aTwo L) ↔
          p ≤ (L + D) / (2 * L + D)) := by
      intro p hpHalf hpOne
      let sp := 2 * p - 1
      let tp := D * (1 - sp) / (2 * sp)
      have hsp : 0 < sp := by dsimp [sp]; nlinarith
      have hthreshold : p ≤ (L + D) / (2 * L + D) ↔ L ≤ tp := by
        constructor
        · intro hp
          have hscaled : p * (2 * L + D) ≤ L + D :=
            (le_div_iff₀ hdenStar).mp hp
          apply (le_div_iff₀ (by positivity : 0 < 2 * sp)).2
          dsimp [tp, sp]
          nlinarith
        · intro ht
          apply (le_div_iff₀ hdenStar).2
          have hscaled := (le_div_iff₀ (by positivity : 0 < 2 * sp)).mp ht
          dsimp [tp, sp] at hscaled
          nlinarith
      constructor
      · intro hinj
        by_contra hp
        have htlt : tp < L := lt_of_not_ge (fun ht => hp (hthreshold.mpr ht))
        let x := max aTwo tp
        let y := (x + L) / 2
        have hxlt : x < L := by
          dsimp [x]
          exact max_lt haL htlt
        have hxy : x < y := by
          dsimp [y]
          exact left_lt_add_div_two.mpr hxlt
        have hylt : y < L := by
          dsimp [y]
          exact add_div_two_lt_right.mpr hxlt
        have hax : aTwo ≤ x := by dsimp [x]; exact le_max_left _ _
        have htx : tp ≤ x := by dsimp [x]; exact le_max_right _ _
        have hx : x ∈ Set.Ico aTwo L := ⟨hax, hxlt⟩
        have hy : y ∈ Set.Ico aTwo L := ⟨hax.trans hxy.le, hylt⟩
        have hty : tp ≤ y := htx.trans hxy.le
        have heq : asymmetricFiberRisk MTwo aTwo p x =
            asymmetricFiberRisk MTwo aTwo p y := by
          rw [truncatedRisk p hpHalf hpOne x hx,
            truncatedRisk p hpHalf hpOne y hy]
          change MTwo * (1 - p) + sp * min x tp =
            MTwo * (1 - p) + sp * min y tp
          rw [min_eq_right htx, min_eq_right hty]
        exact (ne_of_lt hxy) (hinj hx hy heq)
      · intro hp x hx y hy heq
        have ht : L ≤ tp := hthreshold.mp hp
        have hxt : x ≤ tp := hx.2.le.trans ht
        have hyt : y ≤ tp := hy.2.le.trans ht
        rw [truncatedRisk p hpHalf hpOne x hx,
          truncatedRisk p hpHalf hpOne y hy,
          show D * (1 - (2 * p - 1)) / (2 * (2 * p - 1)) = tp by rfl,
          min_eq_left hxt, min_eq_left hyt] at heq
        dsimp [sp] at hsp
        nlinarith
    have hClassification := injectiveClassification piTwo hPiHalf hPiOne
    have hThresholdIdentity :
        (L + D) / (2 * L + D) = (1 + D / U) / 2 := by
      rw [show 2 * L + D = U by rfl]
      field_simp [ne_of_gt hU]
      ring
    have hSlopeBound :
        Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) →
          s ≤ D / U := by
      intro hinj
      have hp := hClassification.mp hinj
      have hscaled : piTwo * (2 * L + D) ≤ L + D :=
        (le_div_iff₀ hdenStar).mp hp
      apply (le_div_iff₀ hU).2
      dsimp [s, U]
      nlinarith
    let piStar := (L + D) / (2 * L + D)
    have hPiStarHalf : 1 / 2 < piStar := by
      dsimp [piStar]
      rw [lt_div_iff₀ hdenStar]
      nlinarith
    have hPiStarOne : piStar ≤ 1 := by
      dsimp [piStar]
      rw [div_le_iff₀ hdenStar]
      nlinarith
    have hPiStarInjective :
        Set.InjOn (asymmetricFiberRisk MTwo aTwo piStar) (Set.Ico aTwo L) :=
      (injectiveClassification piStar hPiStarHalf hPiStarOne).2 (by
        exact le_rfl)
    have hPiStarSlope : 2 * piStar - 1 = D / U := by
      dsimp [piStar]
      rw [show 2 * L + D = U by rfl]
      field_simp [ne_of_gt hU]
      ring
    refine ⟨hFiber, hClassification, hThresholdIdentity, hSlopeBound, ?_, ?_⟩
    · simpa [piStar] using hPiStarInjective
    · simpa [piStar] using hPiStarSlope

#print axioms asymmetric_family_risk_and_injective_queries

end D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
