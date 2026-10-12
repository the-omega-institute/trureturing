/- GID: D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original full posterior and native conditional mass use one shared calibration. -/

import D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
import D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
import D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds
import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
import Mathlib.Analysis.SpecialFunctions.Stirling
import D5.S3.DivergenceSupport.LogSumInequality
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
noncomputable section
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_log
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
private theorem native_row_score_offset {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (i : Fin M) (j : Fin 4)
    (hij : nativeRowCell S e o k l i = some j) :
    score q r e o i -
      ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
        (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))) =
      offsets r (compensation M q r) j := by
  have hi := (native_row_cell_iff S e o k l i j).mp hij
  unfold score
  rw [hi.2.1, hi.2.2]
  fin_cases j <;> simp [offsets] <;> ring
/-- The full original row calibration is the same one shared by the four
cells. The outside index contains every background row and every signal row
outside the rectangle; no row is discarded. -/
theorem native_full_calibration_sum {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ :=
      fun i => score q r e o i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e o i - z0))) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
  let f : Fin M → ℝ := fun i => Real.sigmoid (x + (score q r e o i - z0))
  have hf (j : Fin 4) :
      (∑ i ∈ univ.filter (fun i => nativeRowCell S e o k l i = some j), f i) =
        C j * Real.sigmoid (x + offsets r (compensation M q r) j) := by
    calc
      _ = ∑ _i ∈ nativeCalibrationCells S e o k l j,
          Real.sigmoid (x + offsets r (compensation M q r) j) := by
        apply sum_congr rfl
        intro i hi
        dsimp only [f]
        rw [native_row_score_offset S r e o k l i j (mem_filter.mp hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  have hcounts (j : Fin 4) :
      cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j = C j := by
    fin_cases j <;> dsimp [cellCounts] <;> ring
  have hsum := (sum_fiberwise univ (nativeRowCell S e o k l) f).symm
  rw [Fintype.sum_option] at hsum
  rw [hsum]
  unfold calibratedMean
  change (∑ i with nativeRowCell S e o k l i = none, f i) +
      (∑ j, ∑ i with nativeRowCell S e o k l i = some j, f i) =
    (∑ i : {i : Fin M // nativeRowCell S e o k l i = none}, f i.val) +
      ∑ j, cellCounts (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) j *
        Real.sigmoid (x + offsets r (compensation M q r) j)
  simp only [hcounts]
  congr 1
  · exact (sum_subtype (univ.filter fun i => nativeRowCell S e o k l i = none)
      (fun i => by simp) f)
  · exact sum_congr rfl (fun j _ => hf j)
private theorem native_calibrated_row_parameter {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i : Fin M) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    Real.sigmoid (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / (B0 + t * weight q r e o i) := by
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  have hB0 : 0 < B0 := by
    apply div_pos <;> exact_mod_cast (by omega : 0 < _)
  have hw := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.1 i
  have hexp : Real.exp (score q r e o i - Real.log B0 + Real.log t) =
      t * weight q r e o i / B0 := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hB0, Real.exp_log ht, ← hw.2]
    ring
  dsimp only
  rw [Real.sigmoid_def, Real.exp_neg, hexp]
  change (1 + (t * weight q r e o i / B0)⁻¹)⁻¹ =
    t * weight q r e o i / (B0 + t * weight q r e o i)
  have hden : B0 + t * weight q r e o i ≠ 0 := ne_of_gt (add_pos hB0 (mul_pos ht hw.1))
  field_simp [ne_of_gt ht, ne_of_gt hw.1, ne_of_gt hB0, hden]
  <;> try ring
  rw [← add_mul, mul_inv_cancel₀ hden]
/-- The original calibrated Bernoulli parameters, with their original common
multiplicative parameter, use exactly the same full-row four-cell equation. -/
private theorem native_original_calibration_identification {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e o k l j).card
    let outside : {i : Fin M // nativeRowCell S e o k l i = none} → ℝ :=
      fun i => score q r e o i.val - z0
    (∑ i : Fin M, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  dsimp only
  rw [← native_full_calibration_sum]
  apply sum_congr rfl
  intro i _
  rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]
  congr 1
  ring
/-- The original group-zero posterior center and auxiliary Bernoulli center
both use all rows of the same count cell, including background rows. -/
theorem native_group_zero_centers {M q s : ℕ} (r : ℝ)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) (i0 : Fin M)
    (hi0 : count e o i0 1 = k ∧ count e o i0 (-1) = l) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e o k l 0
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    (∑ i ∈ G, inclusion q r e o i) = (G.card : ℝ) * inclusion q r e o i0 ∧
    (∑ i ∈ G, t * weight q r e o i / (B0 + t * weight q r e o i)) =
      (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t) := by
  classical
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  have hc (i : Fin M) (hi : i ∈ G) :
      count e o i 1 = k ∧ count e o i (-1) = l := by
    have h := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
    simpa using h.2
  have hw (i : Fin M) (hi : i ∈ G) : weight q r e o i = weight q r e o i0 := by
    simp only [weight, (hc i hi).1, (hc i hi).2, hi0.1, hi0.2]
  have ho := ((finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.2.1 o).2.2.2.2
  constructor
  · calc
      _ = ∑ _i ∈ G, inclusion q r e o i0 := by
        apply sum_congr rfl
        intro i hi
        exact le_antisymm ((ho i i0).mpr (le_of_eq (hw i hi)))
          ((ho i0 i).mpr (le_of_eq (hw i hi).symm))
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  · calc
      _ = ∑ _i ∈ G, Real.sigmoid
          ((k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r)) -
              Real.log (((M - q : ℕ) : ℝ) / (q : ℝ)) + Real.log t) := by
        apply sum_congr rfl
        intro i hi
        rw [← native_calibrated_row_parameter r e o hq hqm hr hr1 ha ha1 t ht i]
        simp only [score, (hc i hi).1, (hc i hi).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
/-- The full group-zero size is a fixed background count plus the native
rectangle A count on the same complete collapsed-history fiber. -/
private theorem native_group_zero_count_bridge {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (y : NativeSignalConditionalFiber.Fiber S e o) :
    let All : Support M M := ⟨univ, by simp⟩
    let G := nativeCalibrationCells All e y.val k l 0
    let BG := nativeCalibrationCells All e o k l 0 \ S.val
    G.card = BG.card + RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
  classical
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e y.val k l 0
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  have hG (v : Obs M s e) (i : Fin M) :
      i ∈ nativeCalibrationCells All e v k l 0 ↔
        count e v i 1 = k ∧ count e v i (-1) = l := by
    simp [nativeCalibrationCells, native_row_cell_iff, All]
  have hbg : G \ S.val = BG := by
    ext i
    change i ∈ nativeCalibrationCells All e y.val k l 0 \ S.val ↔
      i ∈ nativeCalibrationCells All e o k l 0 \ S.val
    simp only [Finset.mem_sdiff, hG]
    by_cases hi : i ∈ S.val
    · simp only [hi, not_true_eq_false, and_false]
    · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hi 1,
        NativeSignalConditionalFiber.native_background_row_counts S e o y i hi (-1)]
  have hsig : (G.subtype (fun i => i ∈ S.val)).card =
      RectangleHypergeometricKernel.nativeRectangleACount S e o k l y := by
    congr 1
    ext i
    simp only [mem_subtype, G, hG, RectangleHypergeometricKernel.nativeRectangleACount,
      mem_filter, mem_univ, true_and]
  have hc := card_sdiff_add_card_inter G S.val
  rw [hbg] at hc
  have hs := card_subtype (fun i => i ∈ S.val) G
  simp only [filter_mem_eq_inter] at hs
  rw [hs] at hsig
  exact hc.symm.trans (congrArg (fun n => BG.card + n) hsig)
private theorem sigmoid_log_odds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Real.sigmoid (Real.log (p / (1 - p))) = p := by
  rw [D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_log
    (div_pos hp (sub_pos.mpr hp1))]
  field_simp [ne_of_gt (sub_pos.mpr hp1)]
  <;> ring
/-- The full original group posterior is compared with its common calibrated
center. The mean and variance premises are exactly those of the frozen
posterior-odds theorem; no auxiliary posterior replaces the original one. -/
private theorem native_group_zero_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (r : ℝ), 1 ≤ q → q < M → 0 < r → r < 1 →
        compensation M q r < 1 → ∀ (e : Experiment) (o : Obs M s e) (t : ℝ),
          0 < t → ∀ k l : ℕ,
          let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
          let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
          let V := ∑ i, p i * (1 - p i)
          let All : Support M M := ⟨univ, by simp⟩
          let G := nativeCalibrationCells All e o k l 0
          let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
            (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
          (∑ i, p i) = (q : ℝ) → V0 ≤ V →
            |(∑ i ∈ G, inclusion q r e o i) -
              (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
                C * (G.card : ℝ) / V := by
  classical
  obtain ⟨C, hC, V0, hV0, hpost⟩ :=
    D5.S3.Estimation.SequentialDecisionRisk.UniformPosteriorOdds.result
  refine ⟨C / 4, by positivity, V0, hV0, ?_⟩
  intro M q s r hq hqm hr hr1 ha1 e o t ht k l
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let p := fun i : Fin M => t * weight q r e o i / (B0 + t * weight q r e o i)
  let V := ∑ i, p i * (1 - p i)
  let All : Support M M := ⟨univ, by simp⟩
  let G := nativeCalibrationCells All e o k l 0
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  change (∑ i, p i) = (q : ℝ) → V0 ≤ V → _
  intro hmean hvar
  change |(∑ i ∈ G, inclusion q r e o i) -
    (G.card : ℝ) * Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
      C / 4 * (G.card : ℝ) / V
  have ha : 0 ≤ compensation M q r := by unfold compensation; positivity
  by_cases hG : G.Nonempty
  · obtain ⟨i, hi⟩ := hG
    have hi0 : count e o i 1 = k ∧ count e o i (-1) = l := by
      have hi' := (native_row_cell_iff All e o k l i 0).mp (mem_filter.mp hi).2
      simpa using hi'.2
    have hcenters := native_group_zero_centers r e o k l hq hqm hr hr1 ha ha1 t ht i hi0
    change (∑ j ∈ G, inclusion q r e o j) =
      (G.card : ℝ) * inclusion q r e o i ∧ _ at hcenters
    rw [hcenters.1, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg G.card)]
    have ho := hpost M q s r hq hqm hr hr1 ha1 e o t ht hmean hvar i
    have hlog : score q r e o i - Real.log B0 + Real.log t =
        z0 - Real.log B0 + Real.log t := by
      simp only [score, hi0.1, hi0.2, z0]
    have hlip :=
      D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_lipschitz_certificate.dist_le_mul
      (Real.log (inclusion q r e o i / (1 - inclusion q r e o i)))
      (z0 - Real.log B0 + Real.log t)
    rw [Real.dist_eq, Real.dist_eq, sigmoid_log_odds ho.1 ho.2.1] at hlip
    have herrLog : |Real.log (inclusion q r e o i / (1 - inclusion q r e o i)) -
        (score q r e o i - Real.log B0 + Real.log t)| ≤ C / V := ho.2.2
    rw [hlog] at herrLog
    have herr : |inclusion q r e o i - Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
        (1 / 4 : ℝ) * (C / V) := by
      exact hlip.trans (mul_le_mul_of_nonneg_left herrLog (by norm_num))
    calc
      _ ≤ (G.card : ℝ) * ((1 / 4 : ℝ) * (C / V)) :=
        mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg G.card)
      _ = _ := by ring
  · have he : G = ∅ := not_nonempty_iff_eq_empty.mp hG
    simp [he]
/-- Every row outside the signal rectangle retains both native counts on
one coarse environment fiber. Background rows are included. -/
theorem native_environment_outside_counts {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    count e y.val i 1 = count e z.val i 1 ∧
      count e y.val i (-1) = count e z.val i (-1) ∧
      nativeRowCell S e y.val k l i = none := by
  classical
  by_cases hs : i ∈ S.val
  · let j : {i : Fin M // i ∈ S.val} := ⟨i, hs⟩
    have hn (v : NativeSignalConditionalFiber.Fiber S e o) :
        nativeRowCell S e v.val k l i = none ↔
          j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l v := by
      simp only [RectangleHypergeometricKernel.nativeRectangleRows, mem_filter,
        mem_univ, true_and, j]
      simp only [nativeRowCell, hs, ↓reduceIte]
      split_ifs <;> aesop
    have hz := (hn z).mp hi
    have hV := congrArg Prod.fst henv
    change RectangleHypergeometricKernel.nativeRectangleRows S e o k l y =
      RectangleHypergeometricKernel.nativeRectangleRows S e o k l z at hV
    have hy : j ∉ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y := by
      rwa [hV]
    have he := congrArg (fun v => v.2.1 j) henv
    change (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l y then none
      else some (count e y.val j.val 1, count e y.val j.val (-1))) =
      (if j ∈ RectangleHypergeometricKernel.nativeRectangleRows S e o k l z then none
      else some (count e z.val j.val 1, count e z.val j.val (-1))) at he
    simp only [if_neg hy, if_neg hz, Option.some.injEq, Prod.mk.injEq, j] at he
    exact ⟨he.1, he.2, (hn y).mpr hy⟩
  · rw [NativeSignalConditionalFiber.native_background_row_counts S e o y i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs 1,
      NativeSignalConditionalFiber.native_background_row_counts S e o y i hs (-1),
      NativeSignalConditionalFiber.native_background_row_counts S e o z i hs (-1)]
    exact ⟨rfl, rfl, by simp [nativeRowCell, hs]⟩
/-- The original outside logits are fixed by the same numerical-margin
readout as the native hypergeometric law. -/
private theorem native_environment_outside_score {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (i : Fin M) (hi : nativeRowCell S e z.val k l i = none) :
    score q r e y.val i = score q r e z.val i ∧
      nativeRowCell S e y.val k l i = none := by
  have h := native_environment_outside_counts S e o k l y z henv i hi
  exact ⟨by simp only [score, h.1, h.2.1], h.2.2⟩
/-- The all-row calibration on a native rectangle environment uses one
fixed outside function. Only the four cell multiplicities change. -/
private theorem native_environment_calibration_identification {M q s : ℕ}
    (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let C : Fin 4 → ℝ := fun j => (nativeCalibrationCells S e y.val k l j).card
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
      fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r)
        (C 0 + C 1 + C 2 + C 3) (C 0 + C 2) (C 0 + C 1) (C 0) x := by
  classical
  dsimp only
  rw [native_original_calibration_identification S r e y.val k l hq hqm hr hr1 ha ha1 t ht]
  unfold calibratedMean
  congr 1
  have hn (i : Fin M) : nativeRowCell S e y.val k l i = none ↔
      nativeRowCell S e z.val k l i = none :=
    ⟨fun hi => (native_environment_outside_score S r e o k l z y henv.symm i hi).2,
      fun hi => (native_environment_outside_score S r e o k l y z henv i hi).2⟩
  let E := Equiv.subtypeEquivRight hn
  apply Fintype.sum_equiv E
  intro i
  have hi := native_environment_outside_score S r e o k l z y henv.symm i.val i.property
  simp only [E, Equiv.subtypeEquivRight_apply, hi.1]
/-- The original full calibration on one environment fiber is exactly the
moving four-cell equation with the native N, R, U, and A count. -/
private theorem native_environment_full_calibration {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) (k l : ℕ)
    (y z : NativeSignalConditionalFiber.Fiber S e o)
    (henv : RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l y =
      RectangleHypergeometricKernel.nativeMarginRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (t : ℝ) (ht : 0 < t) :
    let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let x := z0 - Real.log B0 + Real.log t
    let V := RectangleHypergeometricKernel.nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let A := RectangleHypergeometricKernel.nativeRectangleACount S e o k l y
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
      fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r) V.card R U A x := by
  classical
  dsimp only
  rw [native_environment_calibration_identification S r e o k l y z henv
    hq hqm hr hr1 ha ha1 t ht]
  have hc := native_calibration_counts_margins S e o k l y
  dsimp only at hc
  have hV := congrArg (fun v => v.1.card) henv
  have hR := congrArg (fun v => v.2.2.1) henv
  have hU := congrArg (fun v => v.2.2.2) henv
  change (RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).card =
    (RectangleHypergeometricKernel.nativeRectangleRows S e o k l z).card at hV
  change ((RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
    fun i => count e y.val i.val 1 = k).card = _ at hR
  change ((RectangleHypergeometricKernel.nativeRectangleRows S e o k l y).filter
    fun i => count e y.val i.val (-1) = l).card = _ at hU
  congr 1
  · simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) (hc.1.symm.trans hV)
  · simpa only [Nat.cast_add, RectangleHypergeometricKernel.nativeMarginRectangleReadout] using
      congrArg (fun n : ℕ => (n : ℝ)) (hc.2.1.symm.trans hR)
  · simpa only [Nat.cast_add, RectangleHypergeometricKernel.nativeMarginRectangleReadout] using
      congrArg (fun n : ℕ => (n : ℝ)) (hc.2.2.1.symm.trans hU)
  · exact congrArg (fun n : ℕ => (n : ℝ)) hc.2.2.2.symm
end
end D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
noncomputable section
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
/-- The native environment fixes the complete sigmoid equation, including
its derivative. The variance is not supplied as an independent surrogate. -/
theorem native_environment_mean_variance {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let A := nativeRectangleACount S e o k l y
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
      fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A x ∧
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0)) *
      (1 - Real.sigmoid (x + (score q r e y.val i - z0)))) =
        calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val - z0
  have he := (native_minimal_readout_eq_iff S e o k l y z).mp henv
  have hf (u : ℝ) : (∑ i : Fin M, Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A u := by
    let t := Real.exp (u - z0 + Real.log B0)
    have ht : 0 < t := Real.exp_pos _
    have hc := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_environment_full_calibration
      S r e o k l y z he hq hqm hr hr1 ha ha1 t ht
    dsimp only at hc
    have hx : z0 - Real.log B0 + Real.log t = u := by rw [Real.log_exp]; ring
    change (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r) V.card R U A
        (z0 - Real.log B0 + Real.log t) at hc
    rw [hx] at hc
    rw [← hc]
    apply sum_congr rfl
    intro i _
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  refine ⟨hf x, ?_⟩
  have hfun : (∑ i : Fin M, fun u : ℝ => Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A := by
    ext u
    simp only [Finset.sum_apply]
    exact hf u
  have hd := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
    D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv
      (score q r e y.val i - z0) x)
  rw [hfun] at hd
  exact hd.unique (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
    outside r (compensation M q r) V.card R U A x)
/-- The integer target keeps the parity forced by the original harmonic
and count. Half-integer shifts are preserved before any set enlargement. -/
theorem posterior_phase_iff_parity_band (ell t : ℤ) (mu τ : ℝ) :
    (∃ a : ℤ, |(ell : ℝ)*(1/2-mu)-a| ≤ τ) ↔
      ∃ z : ℤ, Int.ModEq 2 z (ell*(1-t)) ∧
        |2*(ell : ℝ)*(mu-(t : ℝ)/2)-z| ≤ 2*τ := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨ell-2*a-ell*t,Int.modEq_iff_dvd.mpr ⟨a,by ring⟩,?_⟩
    have he : 2*(ell : ℝ)*(mu-(t : ℝ)/2)-((ell-2*a-ell*t : ℤ) : ℝ) =
        -2*((ell : ℝ)*(1/2-mu)-a) := by push_cast; ring
    rw [he,abs_mul]
    norm_num
    linarith only [ha]
  · rintro ⟨z,hmod,hz⟩
    obtain ⟨a,ha⟩ := Int.modEq_iff_dvd.mp hmod
    refine ⟨a,?_⟩
    have hez : z = ell-2*a-ell*t := by linear_combination -ha
    rw [hez] at hz
    have he : 2*(ell : ℝ)*(mu-(t : ℝ)/2)-((ell-2*a-ell*t : ℤ) : ℝ) =
        -2*((ell : ℝ)*(1/2-mu)-a) := by push_cast; ring
    rw [he,abs_mul] at hz
    norm_num at hz
    linarith only [hz]
/-- A half-lattice enlargement removes the parity split uniformly for
positive and negative harmonics. The approximation is for the original mu. -/
private theorem posterior_phase_lattice_reduction (ell t : ℤ) (mu bg x τ err : ℝ)
    (happrox : |mu-(bg+(t : ℝ))*Real.sigmoid x| ≤ err)
    (hphase : ∃ z : ℤ, |(ell : ℝ)*(1/2-mu)-z| ≤ τ) :
    ∃ z : ℤ, |2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-(t : ℝ)/2)-z| ≤
      2*τ+2*|(ell : ℝ)| *err := by
  obtain ⟨z,_,hz⟩ := (posterior_phase_iff_parity_band ell t mu τ).mp hphase
  refine ⟨z,?_⟩
  have he : 2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-(t : ℝ)/2)-z =
      (2*(ell : ℝ)*(mu-(t : ℝ)/2)-z)+
        2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-mu) := by ring
  rw [he]
  calc
    _ ≤ |2*(ell : ℝ)*(mu-(t : ℝ)/2)-z|+
        |2*(ell : ℝ)*((bg+(t : ℝ))*Real.sigmoid x-mu)| := abs_add_le _ _
    _ ≤ 2*τ+2*|(ell : ℝ)| *err := by
      rw [abs_mul,abs_mul,abs_sub_comm ((bg+(t : ℝ))*Real.sigmoid x) mu]
      norm_num
      exact add_le_add hz (mul_le_mul_of_nonneg_left happrox (by positivity))
/-- The full original posterior is approximated by the same native shared
root. Its error is proved from frozen posterior odds and the exact all-row
mean and variance identification. -/
private theorem native_environment_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (y z : Fiber S e o),
            nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z →
            ∀ x : ℝ,
            let All : Support M M := ⟨univ, by simp⟩
            let G := nativeCalibrationCells All e y.val k l 0
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
              (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let A := nativeRectangleACount S e o k l y
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
              fun i => score q r e z.val i.val - z0
            calibratedMean outside r (compensation M q r) V.card R U A x = q →
            V0 ≤ calibratedVariance outside r (compensation M q r) V.card R U A x →
              |(∑ i ∈ G, inclusion q r e y.val i) - ((BG.card : ℝ) + A) * Real.sigmoid x| ≤
                C * ((BG.card : ℝ) + A) /
                  calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  obtain ⟨C, hC, V0, hV0, hp⟩ :=
    D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_posterior_approximation
  refine ⟨C, hC, V0, hV0, ?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l y z henv x
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let t := Real.exp (x - z0 + Real.log B0)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val - z0
  let p := fun i : Fin M => t * weight q r e y.val i / (B0 + t * weight q r e y.val i)
  intro hmean hvar
  have ht : 0 < t := Real.exp_pos _
  have hx : z0 - Real.log B0 + Real.log t = x := by rw [Real.log_exp]; ring
  have hrow (i : Fin M) : p i = Real.sigmoid (x + (score q r e y.val i - z0)) := by
    dsimp only [p]
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  have hi := native_environment_mean_variance S r e o k l y z henv hq hqm hr hr1 ha ha1 x
  dsimp only at hi
  have hpm : (∑ i, p i) = (q : ℝ) := by
    simp_rw [hrow]
    exact hi.1.trans hmean
  have hpv : (∑ i, p i * (1 - p i)) =
      calibratedVariance outside r (compensation M q r) V.card R U A x := by
    simp_rw [hrow]
    exact hi.2
  have hh := hp M q s r hq hqm hr hr1 ha1 e y.val t ht k l hpm (hpv.symm ▸ hvar)
  dsimp only at hh
  have hgroup := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_count_bridge
    S e o k l y
  dsimp only at hgroup
  change |(∑ i ∈ nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0,
      inclusion q r e y.val i) -
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) *
        Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
    C * ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) /
      (∑ i, p i * (1 - p i)) at hh
  rw [hx, hpv, hgroup] at hh
  simpa only [Nat.cast_add] using hh
/-- The original posterior phase is covered centrally by a lattice band.
Outside the central interval the original count tail is retained unchanged. -/
theorem native_posterior_central_kernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (z : Fiber S e o) (θ : ℝ → ℝ) (ell : ℤ) (τ w D : ℝ),
            letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
            let All : Support M M := ⟨univ, by simp⟩
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r)) +
              (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let ν : ℝ := (U : ℝ)*R/V.card
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
              fun i => score q r e z.val i.val-z0
            let Env := univ.filter fun y : Fiber S e o =>
              nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
            let Q := fun y : Fiber S e o => ∃ a : ℤ,
              |(ell : ℝ)*(1/2-
                (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i))-a| ≤ τ
            let P := fun t : ℕ => w < |(t : ℝ)-ν| ∨ ∃ a : ℤ,
              |2*(ell : ℝ)*(((BG.card : ℝ)+t)*Real.sigmoid (θ t)-(t : ℝ)/2)-a| ≤
                2*τ+2 * |(ell : ℝ)| * (C*((BG.card : ℝ)+ν+w)/D)
            letI : DecidablePred Q := Classical.decPred Q
            letI : DecidablePred P := Classical.decPred P
            V0 ≤ D →
            (∀ y ∈ Env, |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w →
              calibratedMean outside r (compensation M q r) V.card R U
                (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y)) = q) →
            (∀ y ∈ Env, |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w →
              D ≤ calibratedVariance outside r (compensation M q r) V.card R U
                (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y))) →
            conditionalFiberMass S r e o (Env.filter Q) / conditionalFiberMass S r e o Env ≤
              ∑ t ∈ (range (U+1)).filter P,
                (if t ≤ U then ((R.choose t : ℝ)*((V.card-R).choose (U-t) : ℝ)) /
                  (V.card.choose U : ℝ) else 0) := by
  classical
  obtain ⟨C,hC,V0,hV0,hpost⟩ := native_environment_posterior_approximation
  refine ⟨C,hC,V0,hV0,?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l z θ ell τ w D
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r)) +
    (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let ν : ℝ := (U : ℝ)*R/V.card
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val-z0
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  intro hD hmean hvar
  let Q' : Fiber S e o → Prop := fun y => ∃ a : ℤ,
    |(ell : ℝ) * (1 / 2 -
      (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)) - a| ≤ τ
  let P' : ℕ → Prop := fun t => w < |(t : ℝ)-ν| ∨ ∃ a : ℤ,
    |2 * (ell : ℝ) * (((BG.card : ℝ)+t)*Real.sigmoid (θ t)-(t : ℝ)/2)-a| ≤
      2*τ + 2 * |(ell : ℝ)| * (C*((BG.card : ℝ)+ν+w)/D)
  letI : DecidablePred Q' := Classical.decPred Q'
  letI : DecidablePred P' := Classical.decPred P'
  have hpush : ∀ y, nativeMinimalRectangleReadout S e o k l y =
      nativeMinimalRectangleReadout S e o k l z → Q' y → P' (nativeRectangleACount S e o k l y) := by
    intro y henv hphase
    by_cases hc : |(nativeRectangleACount S e o k l y : ℝ)-ν| ≤ w
    · right
      have hy : y ∈ Env := by simp only [Env,mem_filter,mem_univ,true_and]; exact henv
      have hv := hvar y hy hc
      have happrox := hpost M q s S r e o hq hqm hr hr1 ha ha1 k l y z henv
        (θ (nativeRectangleACount S e o k l y)) (hmean y hy hc) (hD.trans hv)
      have hnum : (BG.card : ℝ)+nativeRectangleACount S e o k l y ≤ (BG.card : ℝ)+ν+w := by
        linarith [(abs_le.mp hc).2]
      have hnum0 : 0 ≤ (BG.card : ℝ)+ν+w :=
        (by positivity : 0 ≤ (BG.card : ℝ)+nativeRectangleACount S e o k l y).trans hnum
      have herr : |(∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i) -
          ((BG.card : ℝ)+nativeRectangleACount S e o k l y)*
            Real.sigmoid (θ (nativeRectangleACount S e o k l y))| ≤ C*((BG.card : ℝ)+ν+w)/D := by
        exact happrox.trans (div_le_div₀ (mul_nonneg hC.le hnum0)
          (mul_le_mul_of_nonneg_left hnum hC.le) (hV0.trans_le hD) hv)
      simpa only [Int.cast_natCast] using posterior_phase_lattice_reduction ell
        (nativeRectangleACount S e o k l y)
        (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)
        BG.card (θ (nativeRectangleACount S e o k l y)) τ (C*((BG.card : ℝ)+ν+w)/D)
        (by simpa only [Int.cast_natCast] using herr) hphase
    · exact Or.inl (lt_of_not_ge hc)
  have hp := native_event_mass_le_kernel S r e o hq hqm hr hr1 ha ha1 k l z Q' P' hpush
  simpa only [Q',P'] using hp
/-- Balanced margins give one root curve on an open neighborhood of the
whole central interval, not a collection of separately chosen roots. -/
theorem balanced_shared_curve {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q δ w : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N) (hδ : 0 < δ) (hw : w ≤ δ^2*N/2)
    (hRlo : δ*N ≤ R) (hRhi : R ≤ (1-δ)*N)
    (hUlo : δ*N ≤ U) (hUhi : U ≤ (1-δ)*N) :
    ∃ θ : ℝ → ℝ, ∀ t : ℝ, |t-U*R/N| ≤ w →
      calibratedMean outside r ε N R U t (θ t) = q ∧
      HasDerivAt θ (-checkerboard r ε (θ t) /
        calibratedVariance outside r ε N R U t (θ t)) t ∧
      (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
      0 < calibratedVariance outside r ε N R U t (θ t) := by
  let ν := U*R/N
  let v := δ^2*N
  have hv : 0 < v := by dsimp [v]; positivity
  have hcells (t : ℝ) (ht : t ∈ Set.Ioo (ν-v) (ν+v)) (j : Fin 4) :
      0 ≤ cellCounts N R U t j := by
    have hc := central_four_cells_lower N R U δ t v hN hδ.le hRlo hRhi hUlo hUhi
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) j
    dsimp [v] at hc
    linarith
  obtain ⟨θ,hθ⟩ := shared_calibration_curve outside r ε N R U q (ν-v) (ν+v)
    hN hq hqM hcells
  refine ⟨θ, fun t ht => ?_⟩
  have hti : t ∈ Set.Ioo (ν-v) (ν+v) := by
    have hb := abs_le.mp ht
    dsimp [v,ν] at *
    constructor <;> nlinarith
  have he := hθ t hti
  refine ⟨he.1,he.2.1,?_,he.2.2⟩
  filter_upwards [isOpen_Ioo.mem_nhds hti] with u hu
  exact (hθ u hu).1
/-- The rectangle and all remaining candidate rows partition the original
M rows, so the root range uses the original support-size condition. -/
theorem native_outside_rectangle_card {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (z : Fiber S e o) :
    Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none} +
      (nativeRectangleRows S e o k l z).card = M := by
  classical
  have hn := (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibration_counts_margins
    S e o k l z).1
  have he := sum_fiberwise (univ : Finset (Fin M)) (nativeRowCell S e z.val k l)
    (fun _ => (1 : ℕ))
  rw [Fintype.sum_option] at he
  simp only [sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin,
    Fin.sum_univ_four] at he
  rw [hn, Fintype.card_subtype]
  simp only [nativeCalibrationCells,add_assoc] at *
  convert he using 1 <;> congr 1
  all_goals ext i; simp only [mem_filter]
end
end D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
namespace D5.S3.Estimation.TimeArrow.OriginalScoreWindow
noncomputable section
set_option maxHeartbeats 800000 in
private theorem compensated_log_bounds (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    |Real.log (1-ε)| ≤ 2*ε ∧ |Real.log (1+ε)| ≤ ε ∧
    Real.log (1-ε) ≤ -ε ∧ Real.log (1+ε) ≤ ε := by
  have hp : 0 < 1-ε := by linarith only [hε1]
  have hm := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hi : (1-ε)⁻¹ ≤ 1+2*ε := by
    apply (inv_le_iff_one_le_mul₀ hp).mpr
    nlinarith only [hε,hε1]
  have hpl := Real.log_le_sub_one_of_pos (by linarith only [hε] : 0 < 1+ε)
  rw [abs_of_nonpos (Real.log_nonpos hp.le (by linarith only [hε])),
    abs_of_nonneg (Real.log_nonneg (by linarith only [hε]))]
  exact ⟨by linarith only [hl,hi],by linarith only [hpl],
    by linarith only [hm],by linarith only [hpl]⟩
set_option maxHeartbeats 800000 in
/-- Integer separation applies to the actual compensated scores. The error
uses the complete count cut and the original uncorrected window center. -/
private theorem count_score_grid_error (k l k0 l0 H Q P : ℕ) (h η ε center raw : ℝ)
    (hQ : 0 < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (hkl : k+l ≤ H) (hraw : raw = k0*(h*((P : ℝ)/Q+η))-(l0 : ℝ)*h) :
    let a := h*((P : ℝ)/Q+η)-Real.log (1-ε)
    let b := -h-Real.log (1+ε)
    let D : ℤ := (P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0)
    |k*a+l*b-center-(h/Q)*D| ≤
      h*η*(H+k0+l0)+2*ε*H+|raw-center| := by
  dsimp only
  obtain ⟨hminus,hplus,_,_⟩ := compensated_log_bounds ε hε hε1
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have he : (k : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      l*(-h-Real.log (1+ε))-center-(h/Q)*
        (((P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0) : ℤ) : ℝ) =
      h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)+(raw-center) := by
    rw [hraw]
    push_cast
    field_simp <;> ring
  rw [he]
  have hk : |(k : ℝ)-k0| ≤ H+k0+l0 := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    rw [abs_le]
    constructor <;> linarith only [hh',(Nat.cast_nonneg l : (0 : ℝ) ≤ l),(Nat.cast_nonneg k : (0 : ℝ) ≤ k),(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0),(Nat.cast_nonneg l0 : (0 : ℝ) ≤ l0)]
  have hcounts : 2*ε*k+ε*l ≤ 2*ε*H := by
    have hh' : (k : ℝ)+(l : ℝ) ≤ H := by exact_mod_cast hkl
    nlinarith only [mul_le_mul_of_nonneg_left hh' hε,(Nat.cast_nonneg l : (0 : ℝ) ≤ l),hε]
  calc
    _ ≤ |h*η*((k : ℝ)-k0)|+|(k : ℝ)*Real.log (1-ε)|+
        |(l : ℝ)*Real.log (1+ε)|+|raw-center| := by
      have h1 := abs_add_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)-l*Real.log (1+ε)) (raw-center)
      have h2 := abs_sub_le (h*η*((k : ℝ)-k0)-(k : ℝ)*Real.log (1-ε)) 0 (l*Real.log (1+ε))
      have h3 := abs_sub_le (h*η*((k : ℝ)-k0)) 0 ((k : ℝ)*Real.log (1-ε))
      simp only [sub_zero,zero_sub,abs_neg] at h2 h3
      linarith only [h1,h2,h3]
    _ ≤ h*η*(H+k0+l0)+2*ε*k+ε*l+|raw-center| := by
      simp only [abs_mul,abs_of_nonneg hh.le,abs_of_nonneg hη.le,
        abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k),abs_of_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
      have hx := mul_le_mul_of_nonneg_left hk (mul_nonneg hh.le hη.le)
      have hm := mul_le_mul_of_nonneg_left hminus (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
      nlinarith only [hx,hm,hp]
    _ ≤ _ := by linarith only [hcounts]
set_option maxHeartbeats 800000 in
/-- The positive original score step separates exact groups, including
negative original grid indices. -/
private theorem compensated_grid_step_pos (Q P : ℕ) (h η ε : ℝ)
    (hPQ : P < Q) (hh : 0 < h) (hη : 0 < η) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2) :
    0 < (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hPQ' : (P : ℝ) < Q := by exact_mod_cast hPQ
  obtain ⟨_,_,hminus,hplus⟩ := compensated_log_bounds ε hε hε1
  have he : (Q : ℝ)*(h*((P : ℝ)/Q+η)-Real.log (1-ε))+
      P*(-h-Real.log (1+ε)) = (Q : ℝ)*h*η-Q*Real.log (1-ε)-P*Real.log (1+ε) := by
    field_simp <;> ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hminus hQ.le
  have hp := mul_le_mul_of_nonneg_left hplus (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hgap : 0 ≤ ((Q : ℝ)-P)*ε := mul_nonneg (by linarith only [hPQ']) hε
  have hpos : 0 < (Q : ℝ)*h*η := by positivity
  nlinarith only [hm,hp,hgap,hpos]
set_option maxHeartbeats 800000 in
private theorem count_zero_score_unique (k l k0 l0 H Q P : ℕ) (a b scale center E : ℝ)
    (hQ : 0 < Q) (hscale : 0 < scale) (hgap : 2*E < scale)
    (hstep : 0 < (Q : ℝ)*a+P*b)
    (hkl : k+l ≤ H) (hbase : k0+l0 ≤ H)
    (herror : ∀ K L : ℕ,K+L ≤ H →
      |(K : ℝ)*a+L*b-center-scale*
        (((P : ℤ)*((K : ℤ)-k0)-(Q : ℤ)*((L : ℤ)-l0) : ℤ) : ℝ)| ≤ E)
    (heq : (k : ℝ)*a+l*b = k0*a+l0*b) : k = k0 ∧ l = l0 := by
  let D : ℤ := (P : ℤ)*((k : ℤ)-k0)-(Q : ℤ)*((l : ℤ)-l0)
  have hi := herror k l hkl
  have hb := herror k0 l0 hbase
  simp only [sub_self,mul_zero,sub_zero,Int.cast_zero] at hb
  have hD : D = 0 := by
    by_contra hn
    have habs : (1 : ℝ) ≤ |(D : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have he : scale*(D : ℝ) = ((k0 : ℝ)*a+l0*b-center)-
        ((k : ℝ)*a+l*b-center-scale*(D : ℝ)) := by rw [heq]; ring
    have hbound : |scale*(D : ℝ)| ≤ 2*E := by
      rw [he]
      calc
        _ ≤ |(k0 : ℝ)*a+l0*b-center|+|(k : ℝ)*a+l*b-center-scale*(D : ℝ)| := abs_sub _ _
        _ ≤ _ := by linarith only [hi,hb]
    rw [abs_mul,abs_of_pos hscale] at hbound
    have hl := mul_le_mul_of_nonneg_left habs hscale.le
    linarith only [hl,hbound,hgap]
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hDreal : (P : ℝ)*((k : ℝ)-k0)-(Q : ℝ)*((l : ℝ)-l0) = 0 := by
    have hd : (D : ℝ) = 0 := by rw [hD]; simp
    simpa only [D,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using hd
  have hlinear : ((Q : ℝ)*a+P*b)*((k : ℝ)-k0) =
      (Q : ℝ)*((k : ℝ)*a+l*b-(k0*a+l0*b))+b*((P : ℝ)*((k : ℝ)-k0)-(Q : ℝ)*((l : ℝ)-l0)) := by ring
  rw [heq,sub_self,hDreal,mul_zero,zero_add,mul_zero] at hlinear
  have hk : (k : ℝ) = k0 := by
    have hh := (mul_eq_zero.mp hlinear).resolve_left hstep.ne'
    linarith only [hh]
  have hl : (l : ℝ) = l0 := by
    rw [hk,sub_self,mul_zero,zero_sub,neg_eq_zero] at hDreal
    have hh := (mul_eq_zero.mp hDreal).resolve_left hQ0
    linarith only [hh]
  exact ⟨by exact_mod_cast hk,by exact_mod_cast hl⟩
set_option maxHeartbeats 1000000 in
/-- Finite original numerical bounds identify the complete exact zero score
group with the A cell over all candidates, including background rows. -/
theorem original_zero_group_eq_all_cell {M s : ℕ} (q : ℕ) (r center width η : ℝ)
    (e : Experiment) (o : Obs M s e) (k0 l0 H Q P : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (hPQ : P < Q) (hη : 0 < η)
    (hε : 0 ≤ compensation M q r) (hε1 : compensation M q r ≤ 1/2)
    (hbase : k0+l0 ≤ H) (hcut : originalCountCut H e o) (hwidth : 0 < width)
    (hlog : Real.log (1+r) = (-Real.log (1-r))*((P : ℝ)/Q+η))
    (herror : (-Real.log (1-r))*η*(H+k0+l0)+2*compensation M q r*H+
      |(k0 : ℝ)*Real.log (1+r)+l0*Real.log (1-r)-center| ≤ width/2)
    (hgrid : (Q : ℝ)*width ≤ (-Real.log (1-r))/4) :
    let value := (k0 : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
      l0*Real.log ((1-r)/(1+compensation M q r))
    originalScoreGroup q r center width value e o =
      nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e o k0 l0 0 := by
  classical
  dsimp only
  let h := -Real.log (1-r)
  let ε := compensation M q r
  let raw := (k0 : ℝ)*Real.log (1+r)+l0*Real.log (1-r)
  let E := h*η*(H+k0+l0)+2*ε*H+|raw-center|
  let a := h*((P : ℝ)/Q+η)-Real.log (1-ε)
  let b := -h-Real.log (1+ε)
  have hh : 0 < h := by
    dsimp [h]
    exact neg_pos.mpr (Real.log_neg (by linarith only [hr1]) (by linarith only [hr]))
  have hQ : 0 < Q := by omega
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha : Real.log ((1+r)/(1-ε)) = a := by
    rw [Real.log_div (by linarith only [hr]) (by linarith only [hε1]),hlog]
  have hb : Real.log ((1-r)/(1+ε)) = b := by
    rw [Real.log_div (by linarith only [hr1]) (by linarith only [hε])]
    dsimp [b,h]
    ring
  have hraw : raw = k0*(h*((P : ℝ)/Q+η))-(l0 : ℝ)*h := by dsimp [raw,h]; rw [hlog] <;> ring
  have he (K L : ℕ) (hKL : K+L ≤ H) :
      |(K : ℝ)*a+L*b-center-(h/Q)*
        (((P : ℤ)*((K : ℤ)-k0)-(Q : ℤ)*((L : ℤ)-l0) : ℤ) : ℝ)| ≤ E :=
    count_score_grid_error K L k0 l0 H Q P h η ε center raw hQ hh hη hε hε1 hKL hraw
  have hstep : 0 < (Q : ℝ)*a+P*b := compensated_grid_step_pos Q P h η ε hPQ hh hη hε hε1
  have hE : E ≤ width/2 := herror
  have hgap : 2*E < h/Q := by
    have hscale := div_pos hh hQreal
    have hsmall : width ≤ (h/Q)/4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
      apply (le_div_iff₀ hQreal).mpr
      nlinarith only [hgrid]
    linarith only [hE,hsmall,hscale]
  have hbaseerror := he k0 l0 hbase
  simp only [sub_self,mul_zero,sub_zero,Int.cast_zero] at hbaseerror
  have hwindow : center-width < (k0 : ℝ)*a+l0*b ∧ (k0 : ℝ)*a+l0*b ≤ center+width := by
    have hx := abs_le.mp hbaseerror
    constructor <;> linarith only [hx.1,hx.2,hE,hwidth]
  ext i
  simp only [originalScoreGroup,originalWindow,nativeCalibrationCells,mem_filter,mem_univ,true_and]
  rw [native_row_cell_iff]
  simp only [mem_univ,true_and,Fin.isValue,Matrix.cons_val_zero,Nat.add_zero]
  rw [ha,hb]
  constructor
  · rintro ⟨_,hscore⟩
    change (count e o i 1 : ℝ)*Real.log ((1+r)/(1-ε))+
      count e o i (-1)*Real.log ((1-r)/(1+ε)) = _ at hscore
    rw [ha,hb] at hscore
    exact count_zero_score_unique (count e o i 1) (count e o i (-1)) k0 l0 H Q P a b
      (h/Q) center E hQ (div_pos hh hQreal) hgap hstep (hcut i) hbase he hscore
  · rintro ⟨hk,hl⟩
    constructor
    · simpa only [score,hk,hl,ε,ha,hb] using hwindow
    · simpa only [score,hk,hl,ε,ha,hb]
private theorem original_count_cut_transfer {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l H : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hH : k+l+2 ≤ H) (hcut : originalCountCut H e z.val) : originalCountCut H e y.val := by
  classical
  intro i
  cases ho : nativeRowCell S e y.val k l i with
  | none =>
    have hmargin := (native_minimal_readout_eq_iff S e o k l z y).mp henv.symm
    have hi := native_environment_outside_counts S e o k l z y hmargin i ho
    rw [←hi.1,←hi.2.1]
    exact hcut i
  | some j =>
    have hi := (native_row_cell_iff S e y.val k l i j).mp ho
    fin_cases j <;> simp at hi <;> omega
/-- A cut witnessed by one anchor holds on its entire original environment;
the conditioning sigma-algebra receives no additional success flag. -/
theorem original_count_cut_same_environment {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l H : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hH : k+l+2 ≤ H) : originalCountCut H e y.val ↔ originalCountCut H e z.val :=
  ⟨original_count_cut_transfer S e o k l H z y henv.symm hH,
    original_count_cut_transfer S e o k l H y z henv hH⟩
end
end D5.S3.Estimation.TimeArrow.OriginalScoreWindow
