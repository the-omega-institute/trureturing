/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleReferenceRatios
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleReferenceRatios
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact adjacent signal masses and compensated background mass share one reference cell. -/

import D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
noncomputable section

private theorem row_reference_successors {M q L : ℕ} (S : Support M q) (r : ℝ)
    (i : Fin M) (k l : ℕ) :
    rowReference S r L i (k + 1, l) =
      ((L : ℝ) * (1 + b r S (.inl i)) / 2 / (k + 1)) * rowReference S r L i (k, l) ∧
    rowReference S r L i (k, l + 1) =
      ((L : ℝ) * (1 - b r S (.inl i)) / 2 / (l + 1)) * rowReference S r L i (k, l) := by
  unfold rowReference
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  constructor <;> field_simp <;> ring

/-- Large central signal counts give simultaneous reference ratios for all
four cells, using the original compensated model rather than a new law. -/
theorem signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (k l : ℕ)
    (hkp : 15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)))
    (hkp' : ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1)
    (hlp : 15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))
    (hlp' : ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1) :
    ∀ j : Fin 4,
      7 / 8 * rowReference S r L i (k, l) ≤
        rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ≤
        9 / 8 * rowReference S r L i (k, l) := by
  have hpos := D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos
    S r κ hκ hr hrκ hcκ hL i (k,l)
  have hk := (row_reference_successors (L := L) S r i k l).1
  have hl := (row_reference_successors (L := L) S r i k l).2
  have hkl := (row_reference_successors (L := L) S r i k (l+1)).1
  simp only [b, if_pos hi] at hk hl hkl
  have hprodlo : 7 / 8 ≤
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) := by
    have hh := mul_le_mul hkp hlp (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith)
    norm_num at hh
    linarith only [hh]
  have hprodhi :
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1 := by
    nlinarith only [hkp, hkp', hlp, hlp',
      mul_nonneg (by linarith : 0 ≤ 1 - ((L : ℝ) * (1 + r) / 2 / (k + 1)))
        (by linarith : 0 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))]
  intro j
  fin_cases j
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 9/8 * rowReference S r L i (k,l)
    constructor <;> nlinarith only [hpos]
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l) ∧
      rowReference S r L i (k+1,l) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hk]
    constructor <;> nlinarith only [hpos, hkp, hkp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l+1) ∧
      rowReference S r L i (k,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hl]
    constructor <;> nlinarith only [hpos, hlp, hlp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l+1) ∧
      rowReference S r L i (k+1,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hkl, hl, ← mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_right hprodlo hpos.le,
      (mul_le_mul_of_nonneg_right hprodhi hpos.le).trans (by nlinarith only [hpos])⟩


theorem original_count_rounding (r : ℝ) (L : ℕ) (hr : 0 < r) (hr1 : r < 1)
    (hL : 1 ≤ L) (hplus : 15 ≤ ((1+r)/2)*(L : ℝ))
    (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    k ≤ L ∧ 0 < k ∧ 0 < l ∧
      15/16 ≤ ((L : ℝ)*(1+r)/2/(k+1)) ∧ ((L : ℝ)*(1+r)/2/(k+1)) ≤ 1 ∧
      15/16 ≤ ((L : ℝ)*(1-r)/2/(l+1)) ∧ ((L : ℝ)*(1-r)/2/(l+1)) ≤ 1 := by
  let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
  let l := L-k
  have ha0 : 0 ≤ ((1+r)/2)*(L : ℝ) := by positivity
  have hklo := Nat.floor_le ha0
  have hkhi := Nat.lt_floor_add_one (((1+r)/2)*(L : ℝ))
  change (k : ℝ) ≤ _ at hklo
  change _ < (k : ℝ)+1 at hkhi
  have hkL : k ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith only [hr1, show (0 : ℝ) ≤ L by positivity]
  have hlr : (l : ℝ) = (L : ℝ)-k := by
    exact Nat.cast_sub hkL
  have hkp : 0 < k := by
    have hh : (0 : ℝ) < k := by linarith only [hplus,hkhi]
    exact_mod_cast hh
  have hlp : 0 < l := by
    have hh : (0 : ℝ) < l := by rw [hlr]; linarith only [hminus,hklo]
    exact_mod_cast hh
  refine ⟨hkL,hkp,hlp,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    nlinarith only [hplus,hklo]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    linarith only [hkhi]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hminus,hkhi]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hklo]

/-- The central four-cell comparison retains the original natural floor
and l=lambda-k. Only explicit lower scale bounds are needed. -/
theorem floored_signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1-κ)
    (hcκ : compensation M q r ≤ 1-κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1+r)/2)*(L : ℝ)) (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    ∀ j : Fin 4, 7/8 * rowReference S r L i (k,l) ≤
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ≤
        9/8 * rowReference S r L i (k,l) := by
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hh := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hh ⊢
  exact signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi _ _
    hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2

/-- The background A mean is exactly the signal A mean times the negative
original A logit. The finite-size compensation and M-q are preserved. -/
theorem background_reference_cell_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (hq : 1 ≤ q) (hqm : q < M) (i j : Fin M)
    (hi : i ∈ S.val) (hj : j ∉ S.val) (k l : ℕ) :
    ((M - q : ℕ) : ℝ) * rowReference S r L j (k,l) =
      ((q : ℝ) * rowReference S r L i (k,l)) *
        Real.exp (-(k * Real.log ((1+r)/(1-compensation M q r)) +
          l * Real.log ((1-r)/(1+compensation M q r)) -
          Real.log (((M-q : ℕ) : ℝ) / q))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hMR : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast (show 0 < M-q by omega)
  rw [reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj (k,l)]
  rw [neg_sub, Real.exp_sub, Real.exp_log (div_pos hMR hqR)]
  field_simp
  <;> ring

end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
