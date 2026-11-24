/- GID: D5/S3/Fourier/Concentration/AggregateCosineBalance
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/AggregateCosineBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Detect failure of shared clipping for the first two real cosine modes. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.LinearCombination

/-! Two tests for the first-minus-second moment of a function of the summed readout. -/

open Finset AddChar

namespace D5.S3.Fourier.Concentration.AggregateCosineBalance

noncomputable def e {q : ℕ} [NeZero q] (k : ZMod q) (m : ℤ) : ℂ :=
  ZMod.stdAddChar ((m : ZMod q) * k)

private theorem mul_e {q : ℕ} [NeZero q] (k : ZMod q) (a b : ℤ) :
    e k a * e k b = e k (a + b) := by
  simp only [e, Int.cast_add, add_mul, map_add_eq_mul]

private theorem sum_e {q : ℕ} [NeZero q] (hq : 7 ≤ q) (m : ℤ)
    (hm : m ≠ 0) (hlo : -6 ≤ m) (hhi : m ≤ 6) :
    (∑ k : ZMod q, e k m) = 0 := by
  have hmod : (m : ZMod q) ≠ 0 := by
    intro h
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m q).mp h
    have hq' : (7 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
    rcases lt_trichotomy b 0 with hneg | heq | hpos
    · have h := mul_le_mul_of_nonneg_left (show b ≤ -1 by omega)
        (show 0 ≤ (q : ℤ) by positivity)
      linarith
    · simp [heq] at hb
      exact hm hb
    · have h := mul_le_mul_of_nonneg_left (show 1 ≤ b by omega)
        (show 0 ≤ (q : ℤ) by positivity)
      linarith
  exact sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hmod)

private theorem sum_e_zero {q : ℕ} [NeZero q] :
    (∑ k : ZMod q, e k 0) = q := by simp [e]

private theorem laurent {q : ℕ} [NeZero q] (k : ZMod q) :
    ((e k 1 + e k (-1)) - (e k 2 + e k (-2))) *
      ((e k 1 + e k (-1)) + (e k 2 + e k (-2))) ^ 2 =
    2 * e k 0 + (e k (-1) + e k 1) - (e k (-2) + e k 2) +
      (e k (-4) + e k 4) - (e k (-5) + e k 5) - (e k (-6) + e k 6) := by
  simp only [pow_two, add_mul, sub_mul, mul_add, mul_e]
  norm_num
  ring

private theorem sum_laurent {q : ℕ} [NeZero q] (hq : 7 ≤ q) :
    (∑ k : ZMod q,
      (((e k 1 + e k (-1)) - (e k 2 + e k (-2))) *
      ((e k 1 + e k (-1)) + (e k 2 + e k (-2))) ^ 2)) = 2 * (q : ℂ) := by
  simp only [laurent, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  have hs (z : ℤ) (h : z ≠ 0) (hl : -6 ≤ z) (hr : z ≤ 6) :=
    sum_e hq z h hl hr
  rw [sum_e_zero, hs (-1) (by decide) (by decide) (by decide),
    hs 1 (by decide) (by decide) (by decide),
    hs (-2) (by decide) (by decide) (by decide),
    hs 2 (by decide) (by decide) (by decide),
    hs (-4) (by decide) (by decide) (by decide),
    hs 4 (by decide) (by decide) (by decide),
    hs (-5) (by decide) (by decide) (by decide),
    hs 5 (by decide) (by decide) (by decide),
    hs (-6) (by decide) (by decide) (by decide),
    hs 6 (by decide) (by decide) (by decide)]
  ring

noncomputable def mode {q : ℕ} (k : ZMod q) (m : ℤ) : ℝ :=
  Real.cos (2 * Real.pi * (m : ℝ) * (k.val : ℝ) / (q : ℝ))

private theorem e_exp {q : ℕ} [NeZero q] (k : ZMod q) (m : ℤ) :
    e k m = Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (k.val : ℂ) / (q : ℂ)) := by
  have hm : ((m * (k.val : ℤ) : ℤ) : ZMod q) = (m : ZMod q) * k := by
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [e, ← hm, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

theorem e_pair {q : ℕ} [NeZero q] (k : ZMod q) (m : ℤ) :
    e k m + e k (-m) = 2 * (mode k m : ℂ) := by
  rw [e_exp, e_exp, mode, Complex.ofReal_cos, Complex.cos]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (k.val : ℂ) / (q : ℂ) =
    (2 * (Real.pi : ℂ) * (m : ℂ) * (k.val : ℂ) / (q : ℂ)) * Complex.I by ring,
    show 2 * (Real.pi : ℂ) * Complex.I * (-(m : ℂ)) * (k.val : ℂ) / (q : ℂ) =
    -(2 * (Real.pi : ℂ) * (m : ℂ) * (k.val : ℂ) / (q : ℂ)) * Complex.I by ring]
  ring

private theorem cubic_readout {q : ℕ} [NeZero q] (hq : 7 ≤ q) :
    (∑ k : ZMod q, (mode k 1 - mode k 2) * (mode k 1 + mode k 2) ^ 2) =
      (q : ℝ) / 4 := by
  have h := sum_laurent hq
  simp only [e_pair] at h
  have hs (k : ZMod q) :
      (2 * (mode k 1 : ℂ) - 2 * (mode k 2 : ℂ)) *
          (2 * (mode k 1 : ℂ) + 2 * (mode k 2 : ℂ)) ^ 2 =
        8 * (((mode k 1 - mode k 2) * (mode k 1 + mode k 2) ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [hs, ← mul_sum, ← Complex.ofReal_sum] at h
  have hr : (8 : ℝ) * (∑ k : ZMod q, (mode k 1 - mode k 2) * (mode k 1 + mode k 2) ^ 2) =
      2 * (q : ℝ) := by exact_mod_cast h
  linarith

theorem mode_double {q : ℕ} (k : ZMod q) :
    mode k 2 = 2 * (mode k 1) ^ 2 - 1 := by
  dsimp [mode]
  rw [← Real.cos_two_mul]
  congr 1
  push_cast
  ring

private theorem mode_one_interval {q : ℕ} [NeZero q] (hq : 7 ≤ q) :
    1 / 2 < mode (1 : ZMod q) 1 ∧ mode (1 : ZMod q) 1 < 1 := by
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq
  let θ := 2 * Real.pi / (q : ℝ)
  have hθ : 0 < θ := by positivity
  have hθ' : θ < Real.pi / 3 := by
    change 2 * Real.pi / (q : ℝ) < Real.pi / 3
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < q)).2
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr (show (6 : ℝ) < q by linarith))]
  have hθmem : θ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hθ.le, by linarith [Real.pi_pos]⟩
  have hthird : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hlo := Real.strictAntiOn_cos hθmem hthird hθ'
  have hhi := Real.strictAntiOn_cos hzero hθmem hθ
  rw [Real.cos_pi_div_three] at hlo
  rw [Real.cos_zero] at hhi
  simpa only [mode, ZMod.val_one'' (by omega : q ≠ 1), Int.cast_one, Nat.cast_one, mul_one, θ]
    using And.intro hlo hhi

private theorem positive_readout_at_zero {q : ℕ} [NeZero q] (hq : 7 ≤ q) :
    0 < (∑ k : ZMod q, (mode k 1 - mode k 2) * max 0 (mode k 1 + mode k 2)) := by
  have hd (k : ZMod q) : mode k 1 - mode k 2 = (1 - mode k 1) * (2 * mode k 1 + 1) := by
    rw [mode_double]
    ring
  have hs (k : ZMod q) : mode k 1 + mode k 2 = (2 * mode k 1 - 1) * (mode k 1 + 1) := by
    rw [mode_double]
    ring
  apply sum_pos'
  · intro k _
    by_cases h : 1 / 2 < mode k 1
    · rw [hd]
      refine mul_nonneg (mul_nonneg ?_ (by linarith)) (le_max_left _ _)
      exact sub_nonneg.mpr (Real.cos_le_one _)
    · rw [hs, max_eq_left (mul_nonpos_of_nonpos_of_nonneg (by linarith) ?_), mul_zero]
      have hc : -(1 : ℝ) ≤ mode k 1 := Real.neg_one_le_cos _
      linarith
  · obtain ⟨hlow, hhigh⟩ := mode_one_interval hq
    refine ⟨1, mem_univ _, ?_⟩
    rw [hd, hs]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (lt_of_lt_of_le
      (mul_pos (by linarith) (by linarith)) (le_max_right _ _))

/-- The summed readout detects unequal moments at cutoff zero on every cycle of size at
least seven. Its squared readout has an exact signed moment from the cubic resonance. -/
theorem aggregate_cosine_imbalance {q : ℕ} [NeZero q] (hq : 7 ≤ q) :
    let c := fun k : ZMod q => Real.cos (2 * Real.pi * (k.val : ℝ) / q)
    let d := fun k : ZMod q => Real.cos (4 * Real.pi * (k.val : ℝ) / q)
    let square := fun x : ℝ => x ^ 2
    (∑ k, (c k - d k) * square (c k + d k)) = (q : ℝ) / 4 ∧
      0 < ∑ k, (c k - d k) * max 0 (c k + d k) := by
  have hc (k : ZMod q) : mode k 1 = Real.cos (2 * Real.pi * (k.val : ℝ) / q) := by
    simp only [mode, Int.cast_one, mul_one]
  have hd (k : ZMod q) : mode k 2 = Real.cos (4 * Real.pi * (k.val : ℝ) / q) := by
    unfold mode
    push_cast
    congr 1
    ring
  simpa only [hc, hd] using And.intro (cubic_readout hq) (positive_readout_at_zero hq)

end D5.S3.Fourier.Concentration.AggregateCosineBalance
