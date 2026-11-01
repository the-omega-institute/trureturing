/- GID: D5/S3/Estimation/CorrelationWeightSpectralBound
   generality: G
   mirror-B: D5/B/S3/Estimation/CorrelationWeightSpectralBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Two leading spectral values force a strict centered second-moment bound. -/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! A centered finite-spectrum inequality used by the correlation weight obstruction. -/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Estimation.CorrelationWeightSpectralBound

private lemma two_point_energy {n : ℕ} (hn : 3 ≤ n) (μ : Fin n → ℝ)
    (hsum : ∑ j, μ j = 0) (i j : Fin n) (hij : i ≠ j) :
    (n : ℝ) * (μ i + μ j) ^ 2 ≤
      2 * ((n : ℝ) - 2) * ∑ k, μ k ^ 2 := by
  classical
  let s := (univ.erase i).erase j
  have hj : j ∈ univ.erase i := mem_erase.mpr ⟨hij.symm, mem_univ _⟩
  have hcard : (s.card : ℝ) = (n : ℝ) - 2 := by
    simp only [s, card_erase_of_mem hj, card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
    ring
  have hrest : ∑ k ∈ s, μ k = -(μ i + μ j) := by
    have hi := sum_erase_add univ μ (mem_univ i)
    have hj := sum_erase_add (univ.erase i) μ hj
    dsimp only [s]
    linarith
  have hrestsq : (∑ k ∈ s, μ k ^ 2) + (μ i ^ 2 + μ j ^ 2) =
      ∑ k, μ k ^ 2 := by
    have hi := sum_erase_add univ (fun k => μ k ^ 2) (mem_univ i)
    have hj := sum_erase_add (univ.erase i) (fun k => μ k ^ 2) hj
    dsimp only [s]
    linarith
  have hcs := sum_mul_sq_le_sq_mul_sq s μ (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one, hrest, hcard,
    neg_sq] at hcs
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) - 2 := by linarith
  have hpair := mul_nonneg hn0 (sq_nonneg (μ i - μ j))
  nlinarith [hrestsq]

private lemma top_pair_of_weights {n : ℕ} (hn : 3 ≤ n) (μ w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (i : Fin n)
    (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    ∃ j, j ≠ i ∧ 2 * (∑ k, μ k * w k) ≤ μ i + μ j := by
  classical
  have hne : (univ.erase i).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, hmax⟩ := exists_max_image (univ.erase i) μ hne
  refine ⟨j, (mem_erase.mp hj).1, ?_⟩
  have hsumle : ∑ k ∈ univ.erase i, μ k * w k ≤
      μ j * ∑ k ∈ univ.erase i, w k := by
    rw [mul_sum]
    exact sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hmax k hk) (hw k)
  have hsw := sum_erase_add univ w (mem_univ i)
  rw [hsum] at hsw
  have hrest : ∑ x ∈ univ.erase i, w x = 1 - w i := by linarith
  rw [hrest] at hsumle
  have hsm := sum_erase_add univ (fun k => μ k * w k) (mem_univ i)
  have hdiff := mul_nonneg (sub_nonneg.mpr (htop j))
    (show 0 ≤ 1 / 2 - w i by linarith)
  nlinarith

/-- A top spectral weight below one half forces a larger centered second moment. -/
theorem centered_energy_strict {n : ℕ} (hn : 3 ≤ n) (c σ : ℝ) (hc : 0 < c)
    (μ w : Fin n → ℝ) (hμ : ∑ j, μ j = 0)
    (henergy : ∑ j, μ j ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2))
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hrayleigh : ∑ j, μ j * w j = ((n : ℝ) - 1) * c)
    (i : Fin n) (htop : ∀ j, μ j ≤ μ i) (hhalf : w i < 1 / 2) :
    c ^ 2 < σ ^ 2 := by
  obtain ⟨j, hji, hpair⟩ := top_pair_of_weights hn μ w hw hsum i htop hhalf
  have hbound := two_point_energy hn μ hμ i j hji.symm
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  rw [hrayleigh] at hpair
  have hpair0 : 0 < μ i + μ j := lt_of_lt_of_le (by positivity) hpair
  have hsquare : (2 * ((n : ℝ) - 1) * c) ^ 2 ≤ (μ i + μ j) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  rw [henergy] at hbound
  have hlarge : 2 * (n : ℝ) * ((n : ℝ) - 1) ^ 2 * c ^ 2 ≤
      ((n : ℝ) - 2) * (n : ℝ) * ((n : ℝ) - 1) * (c ^ 2 + σ ^ 2) := by
    nlinarith only [hbound,
      mul_le_mul_of_nonneg_left hsquare (show 0 ≤ (n : ℝ) by positivity)]
  have hcancel : 2 * ((n : ℝ) - 1) * c ^ 2 ≤
      ((n : ℝ) - 2) * (c ^ 2 + σ ^ 2) := by
    have hnpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by positivity
    apply (mul_le_mul_iff_right₀ hnpos).mp
    nlinarith only [hlarge]
  by_contra h
  have hle : σ ^ 2 ≤ c ^ 2 := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left hle hn2.le
  nlinarith [sq_pos_of_pos hc]

end D5.S3.Estimation.CorrelationWeightSpectralBound
