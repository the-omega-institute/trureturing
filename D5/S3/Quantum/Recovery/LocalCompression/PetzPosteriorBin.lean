/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzPosteriorBin
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzPosteriorBin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted square bins control the RMS and mean gap of the Petz posteriors. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import OmegaBuild.Commands

/-! Scalar and squared Euclidean estimates for commuting-reference Petz posterior bins. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBin

private theorem weighted_rms_sub_mean_interval {ι : Type*} [Fintype ι]
    (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hy : ∀ i, lo ≤ y i ∧ y i ≤ hi) :
    let μ := ∑ i, w i * y i
    let t := Real.sqrt (∑ i, w i * y i ^ 2)
    0 ≤ t - μ ∧ (2 * lo) * (t - μ) ≤ (hi - lo) ^ 2 / 4 := by
  let μ := ∑ i, w i * y i
  let ν := ∑ i, w i * y i ^ 2
  let t := Real.sqrt ν
  change 0 ≤ t - μ ∧ (2 * lo) * (t - μ) ≤ (hi - lo) ^ 2 / 4
  have hμ : 0 ≤ μ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hlo.trans (hy i).1)
  have hcs : μ ^ 2 ≤ ν := by
    simpa only [hsum, one_mul, μ, ν] using
      (Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (r := fun i => w i * y i) (f := w) (g := fun i => w i * y i ^ 2)
        (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg (y i)))
        (fun i _ => le_of_eq (by ring)))
  have htSq : t ^ 2 = ν := Real.sq_sqrt ((sq_nonneg μ).trans hcs)
  have hμt : μ ≤ t := by
    apply (sq_le_sq₀ hμ (Real.sqrt_nonneg ν)).mp
    rw [htSq]
    exact hcs
  have hsecant : ν ≤ (lo + hi) * μ - lo * hi := calc
    ν ≤ ∑ i, ((lo + hi) * (w i * y i) - (lo * hi) * w i) := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_nonneg (hw i)
        (mul_nonneg (sub_nonneg.mpr (hy i).1) (sub_nonneg.mpr (hy i).2))
      nlinarith only [h]
    _ = (lo + hi) * μ - lo * hi := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_one, μ]
  have hvar : t ^ 2 - μ ^ 2 ≤ (hi - lo) ^ 2 / 4 := by
    nlinarith only [htSq, hsecant, sq_nonneg (hi + lo - 2 * μ)]
  have hsum_lower : 2 * lo ≤ t + μ := by
    have hμlo : lo ≤ μ := by
      dsimp [μ]
      have h := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hy i).1 (hw i))
      simpa [hsum] using h
    have hμt' : μ ≤ t := hμt
    nlinarith
  have hprod : (t - μ) * (t + μ) = t ^ 2 - μ ^ 2 := by ring
  have hmul := mul_le_mul_of_nonneg_left hsum_lower (sub_nonneg.mpr hμt)
  exact ⟨sub_nonneg.mpr hμt, by
    rw [← hprod]
    exact hmul.trans hvar⟩

/-- The weighted root mean square exceeds the arithmetic mean by at most
`9 / (8 * L ^ 2)` on a square bin, including the bin with lower endpoint zero. -/
theorem weighted_square_bin_rms_sub_mean_le {ι : Type*} [Fintype ι]
    (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (a L : ℕ) (hL : 0 < L)
    (hy : ∀ i, ((a : ℝ) / L) ^ 2 ≤ y i ∧ y i ≤ (((a : ℝ) + 1) / L) ^ 2) :
    let gap := Real.sqrt (∑ i, w i * y i ^ 2) - ∑ i, w i * y i
    0 ≤ gap ∧ gap ≤ 9 / (8 * (L : ℝ) ^ 2) := by
  let k : ℝ := ((L : ℝ) ^ 2)⁻¹
  let lo : ℝ := (a : ℝ) ^ 2 * k
  let hi : ℝ := ((a : ℝ) + 1) ^ 2 * k
  let gap := Real.sqrt (∑ i, w i * y i ^ 2) - ∑ i, w i * y i
  change 0 ≤ gap ∧ gap ≤ 9 / (8 * (L : ℝ) ^ 2)
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hk : 0 < k := inv_pos.mpr (pow_pos hLr 2)
  have hlo : 0 ≤ lo := mul_nonneg (sq_nonneg _) hk.le
  have hhi : 0 < hi := mul_pos (by positivity) hk
  have hbins : ∀ i, lo ≤ y i ∧ y i ≤ hi := by
    intro i
    simpa only [lo, hi, k, div_pow, div_eq_mul_inv] using hy i
  obtain ⟨hgap, hscaled⟩ := weighted_rms_sub_mean_interval w y hw hsum hlo hbins
  refine ⟨hgap, ?_⟩
  by_cases ha : a = 0
  · subst a
    have hsq : ∑ i, w i * y i ^ 2 ≤ hi ^ 2 := by
      have h := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (sq_le_sq₀ (hbins i).1 (hbins i).2).2 (hw i))
      simpa [hsum] using h
    have htHi : Real.sqrt (∑ i, w i * y i ^ 2) ≤ hi := by
      nlinarith [Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw i) (sq_nonneg (y i)))]
    have hgap_hi : gap ≤ hi := by
      dsimp [gap]
      linarith [htHi]
    have hhi_k : hi = k := by
      dsimp [hi]
      ring
    calc
      gap ≤ hi := hgap_hi
      _ = k := hhi_k
      _ ≤ 9 / (8 * (L : ℝ) ^ 2) := by
        dsimp [k]
        field_simp
        norm_num
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    have hlo_pos : 0 < lo := by
      dsimp [lo]
      positivity
    have hbound : gap ≤ (hi - lo) ^ 2 / (8 * lo) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * lo)).2
      nlinarith [hscaled]
    have hratio : (2 * (a : ℝ) + 1) ^ 2 ≤ 9 * (a : ℝ) ^ 2 := by
      have ha_real : (1 : ℝ) ≤ a := by exact_mod_cast ha_pos
      nlinarith [sq_nonneg ((a : ℝ) - 1)]
    calc
      gap ≤ (hi - lo) ^ 2 / (8 * lo) := hbound
      _ = ((2 * (a : ℝ) + 1) ^ 2) /
          (8 * (a : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
        dsimp [hi, lo, k]
        field_simp
        ring
      _ ≤ 9 / (8 * (L : ℝ) ^ 2) := by
        field_simp
        nlinarith

/-- The squared Euclidean distance between the coordinatewise root mean square
of the flag posteriors and their weighted mean. -/
theorem weighted_square_bin_vector_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (y : ι → κ → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (a : κ → ℕ) (L : ℕ) (hL : 0 < L)
    (hy : ∀ j i, ((a j : ℝ) / L) ^ 2 ≤ y i j ∧
      y i j ≤ (((a j : ℝ) + 1) / L) ^ 2) :
    ∑ j, (Real.sqrt (∑ i, w i * (y i j) ^ 2) - ∑ i, w i * y i j) ^ 2 ≤
      (Fintype.card κ : ℝ) * (9 / (8 * (L : ℝ) ^ 2)) ^ 2 := by
  calc
    _ ≤ ∑ _j : κ, (9 / (8 * (L : ℝ) ^ 2)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      obtain ⟨hgap, hbound⟩ :=
        weighted_square_bin_rms_sub_mean_le w (fun i => y i j) hw hsum (a j) L hL (hy j)
      exact pow_le_pow_left₀ hgap hbound 2
    _ = _ := by simp [nsmul_eq_mul]

end D5.S3.Quantum.Recovery.LocalCompression.PetzPosteriorBin
