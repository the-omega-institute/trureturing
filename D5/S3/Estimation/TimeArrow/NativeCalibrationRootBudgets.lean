/- GID: D5/S3/Estimation/TimeArrow/NativeCalibrationRootBudgets
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeCalibrationRootBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native complete reference deviations control the same all-row calibration root. -/

import D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
import D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
open private
  D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.root_box_of_residual
  D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.sigmoid_variance_tilt
from D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
noncomputable section

private theorem all_row_root_from_residual {M : ℕ} (a : Fin M → ℝ)
    (q x v b : ℝ) (hM : 0 < M) (hv : 0 < v)
    (hroot : (∑ i, Real.sigmoid (x + a i)) = q)
    (hres : |(∑ i, Real.sigmoid (a i)) - q| ≤ b)
    (hvar : v ≤ ∑ i, Real.sigmoid (a i) * (1 - Real.sigmoid (a i)))
    (hsmall : b ≤ v / 2 * Real.log 2) :
    |x| ≤ Real.log 2 ∧ |x| ≤ 2 * b / v ∧
      v / 2 ≤ ∑ i, Real.sigmoid (x + a i) * (1 - Real.sigmoid (x + a i)) ∧
      (∑ i, Real.sigmoid (x + a i) * (1 - Real.sigmoid (x + a i))) ≤ q := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let F := fun u : ℝ => ∑ i, Real.sigmoid (u + a i)
  let V := fun u : ℝ => ∑ i, Real.sigmoid (u + a i) * (1 - Real.sigmoid (u + a i))
  let d := Real.log (2 : ℝ)
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hder (u : ℝ) : HasDerivAt F (V u) u := by
    have hh := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
      D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv (a i) u)
    have he : (∑ i : Fin M, fun z : ℝ => Real.sigmoid (z + a i)) = F := by
      ext z
      simp only [Finset.sum_apply, F]
    rw [he] at hh
    exact hh
  have hV (u : ℝ) : 0 < V u := by
    exact sum_pos (fun i _ => mul_pos (Real.sigmoid_pos _)
      (sub_pos.mpr (Real.sigmoid_lt_one _))) univ_nonempty
  have hmono : StrictMono F := strictMono_of_deriv_pos fun u => by
    rw [(hder u).deriv]
    exact hV u
  have htilt (u : ℝ) (hu : |u| ≤ d) :
      1 / 2 ≤ Real.exp (-u) ∧ Real.exp (-u) ≤ 2 := by
    have hh := abs_le.mp hu
    constructor
    · calc
        1 / 2 = Real.exp (-d) := by simp [d, Real.exp_neg, Real.exp_log]
        _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith only [hh.2])
    · calc
        Real.exp (-u) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith only [hh.1])
        _ = 2 := Real.exp_log (by norm_num)
  have hlower (u : ℝ) (hu : |u| ≤ d) : v / 2 ≤ V u := by
    have ht := htilt u hu
    have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
      (D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.sigmoid_variance_tilt
        (a i) u ht.1 ht.2).1)
    rw [← sum_div] at hh
    simp only [add_comm] at hh
    have hb := mul_le_mul_of_nonneg_left hvar (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    dsimp [V]
    linarith only [hh, hb]
  have hb := D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.root_box_of_residual
    F q 0 x d (v / 2) b hd (by positivity) hmono
    (fun u _ => (hder u).continuousAt.continuousWithinAt)
    (fun u _ => (hder u).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hder u).deriv]
      have hh := interior_subset hu
      exact hlower u (abs_le.mpr (by constructor <;> linarith only [hh.1, hh.2])))
    hroot (by simpa only [F, zero_add] using hres) hsmall
  simp only [sub_zero] at hb
  refine ⟨hb.1, ?_, hlower x hb.1, ?_⟩
  · apply (le_div_iff₀ hv).mpr
    nlinarith only [hb.2]
  · rw [← hroot]
    exact sum_le_sum fun i _ => mul_le_of_le_one_right (Real.sigmoid_nonneg _)
      (by linarith only [Real.sigmoid_nonneg (x + a i)])

/-- The original pair and path laws share a probability budget for the full
calibration root and its variance. The reference lower variance is evaluated
at the complete fixed count-level calibration. -/
theorem native_calibration_root_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ v b : ℝ, 0 < v → 0 < b →
          let p := referenceParameter M q r
          let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
          v ≤ V → b ≤ v / 4 * Real.log 2 →
          ∀ x : Obs M (2 * M * L) e → ℝ,
          (∀ o, (∑ k : Fin M, Real.sigmoid (x o + score q r e o k -
            Real.log (((M - q : ℕ) : ℝ) / q))) = q) →
          let D := fun o => ∑ k : Fin M,
            Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)) *
              (1 - Real.sigmoid (x o + score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (∑ o, if 4 * b / v < |x o| ∨ D o < v / 4 ∨ q < D o
            then probability r e S o else 0) ≤ B / b ^ 2 + B / (v / 2) ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    native_reference_calibration_deviation κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj v b hv hb
  dsimp only
  intro hV hbudget x hx
  let p := referenceParameter M q r
  let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
  let P := fun o : Obs M (2 * M * L) e =>
    ∑ k : Fin M, p (count e o k 1, count e o k (-1))
  let D0 := fun o : Obs M (2 * M * L) e =>
    ∑ k : Fin M, p (count e o k 1, count e o k (-1)) *
      (1 - p (count e o k 1, count e o k (-1)))
  have hdev := (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM
    S e i j hi hj b (v / 2) hb (by positivity)).2.2
  apply le_trans _ hdev
  apply sum_le_sum
  intro o _
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S o
  by_cases hbad : b < |P o - q| ∨ v / 2 < |D0 o - V|
  · simp only [hbad, if_true]
    split_ifs <;> linarith only [hp]
  · have hgood := not_or.mp hbad
    have hmean : |P o - q| ≤ b := le_of_not_gt hgood.1
    have hvar : v / 2 ≤ D0 o := by
      have hh := abs_le.mp (le_of_not_gt hgood.2)
      linarith only [hh.1, hV]
    have hh := all_row_root_from_residual
      (fun k => score q r e o k - Real.log (((M - q : ℕ) : ℝ) / q))
      q (x o) (v / 2) b (by omega) (by positivity)
      (by simpa only [add_sub_assoc] using hx o)
      (by simpa only [P, p, referenceParameter, score] using hmean)
      (by simpa only [D0, p, referenceParameter, score] using hvar)
      (by linarith only [hbudget])
    have hroot : |x o| ≤ 4 * b / v := by
      convert hh.2.1 using 1 <;> field_simp <;> ring
    have hvarroot := hh.2.2
    simp only [hbad, if_false]
    split_ifs with hfail
    · rcases hfail with hfail | hfail | hfail
      · exact False.elim (not_lt_of_ge hroot hfail)
      · exact False.elim (not_lt_of_ge (by simpa only [add_sub_assoc, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hvarroot.1) hfail)
      · exact False.elim (not_lt_of_ge (by simpa only [add_sub_assoc] using hvarroot.2) hfail)
    · exact le_rfl

end
end D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
