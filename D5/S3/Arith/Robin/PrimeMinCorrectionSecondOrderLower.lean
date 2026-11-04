/- GID: D5/S3/Arith/Robin/PrimeMinCorrectionSecondOrderLower
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimeMinCorrectionSecondOrderLower
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: A uniform three-term lower correction for every initial prime support. -/

import D5.S3.Arith.Robin.PrimeMinCorrectionLower
import D5.S3.Arith.Robin.EulerLayer.EulerLayerRootSecondOrder
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower

open Finset Filter
open scoped Topology Chebyshev
open EulerLayerRootSecondOrder OriginalEndpointPrimeTail

noncomputable section

/-- The normalized implicit equation gives a uniform quadratic root error. -/
private theorem root_error {h x : ℝ} (hh : 0 ≤ h) (hx : 1 ≤ x)
    (hxs : x ≤ Real.sqrt 2)
    (heq : x ^ 2 * (1 + 2 * h * Real.log x) = 2) :
    |x - Real.sqrt 2| ≤ h ∧
      |x - Real.sqrt 2 + (Real.sqrt 2 * Real.log 2 / 2) * h| ≤ 4 * h ^ 2 := by
  let s := Real.sqrt 2
  let b := Real.log 2
  let u := Real.log x
  let d := s - x
  let q := x ^ 2 / (x + s)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs1 : 1 ≤ s := by nlinarith
  have hs15 : s < 3 / 2 := by nlinarith
  have hb0 : 0 ≤ b := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hb1 : b < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    dsimp [b]; linarith
  have hx0 : 0 < x := by linarith
  have hden : 0 < x + s := by positivity
  have hv : Real.log s = b / 2 := Real.log_sqrt (by norm_num)
  have hu0 : 0 ≤ u := Real.log_nonneg hx
  have huv : u ≤ b / 2 := by simpa only [hv] using Real.log_le_log hx0 hxs
  have hd0 : 0 ≤ d := sub_nonneg.mpr hxs
  have hq0 : 0 ≤ q := div_nonneg (sq_nonneg x) hden.le
  have hqx : 2 * q ≤ x := by
    dsimp [q]
    apply (mul_div_le_iff₀ hden).mpr
    nlinarith
  have hqs : q ≤ s / 2 := by linarith
  have hqdiff : 0 ≤ s / 2 - q ∧ s / 2 - q ≤ d := by
    constructor
    · linarith
    · dsimp [q, d]
      apply (sub_le_iff_le_add).mpr
      apply (le_div_iff₀' hden).mp ?_
      nlinarith
  have hugap : 0 ≤ b / 2 - u ∧ b / 2 - u ≤ d := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hs0 hx0)
    rw [Real.log_div hs0.ne' hx0.ne', hv] at ht
    have hgap : b / 2 - u ≤ (s - x) / x := by dsimp [u] at *; linarith
    constructor
    · linarith
    · have hdiv : (s - x) / x ≤ s - x := div_le_self hd0 hx
      exact hgap.trans hdiv
  have hdu : d = h * (2 * q * u) := by
    apply (mul_right_cancel₀ hden.ne')
    have hqq : q * (x + s) = x ^ 2 := div_mul_cancel₀ _ hden.ne'
    dsimp [d, s, u] at *
    nlinarith only [heq, hs2, hqq]
  have hfu : 0 ≤ 2 * q * u := by positivity
  have hf1 : 2 * q * u ≤ 1 := by
    calc
      2 * q * u ≤ s * (b / 2) :=
        mul_le_mul (by linarith : 2 * q ≤ s) huv hu0 hs0.le
      _ ≤ 1 := by nlinarith
  have hd : d ≤ h := by rw [hdu]; exact mul_le_of_le_one_right hh hf1
  have hfgap : 0 ≤ s * b / 2 - 2 * q * u ∧
      s * b / 2 - 2 * q * u ≤ 4 * d := by
    have ha := mul_le_mul_of_nonneg_right hqdiff.2 hb0
    have hb := mul_le_mul_of_nonneg_left hugap.2 (by positivity : 0 ≤ 2 * q)
    have hc := mul_le_mul_of_nonneg_right (by linarith : 2 * q ≤ s) hd0
    constructor
    · nlinarith [mul_le_mul (by linarith : 2 * q ≤ s) huv hu0 hs0.le]
    · nlinarith
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hxs)]
    change d ≤ h
    exact hd
  · have hid : x - s + (s * b / 2) * h = h * (s * b / 2 - 2 * q * u) := by
      dsimp [d] at hdu
      linarith
    change |x - s + (s * b / 2) * h| ≤ 4 * h ^ 2
    rw [hid, abs_of_nonneg (mul_nonneg hh hfgap.1)]
    have := mul_le_mul_of_nonneg_left hfgap.2 hh
    nlinarith [mul_le_mul_of_nonneg_left hd hh]

/-- The real root belongs to the finite head, including when it is prime. -/
private theorem finite_root_prime_min_lower {X ρ : ℝ} {P : ℕ}
    (hX : 1 < X) (hρ : 1 < ρ)
    (heq : ρ ^ 2 * Real.log ρ = X * Real.log X) (hP : ρ ≤ (P : ℝ)) :
    θ ρ / (X * Real.log X) +
      (∑ p ∈ (Ioc ⌊ρ⌋₊ P).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      ∑ p ∈ Nat.primesLE P, min (Real.log p / (X * Real.log X))
        (-Real.log (1 - (p : ℝ)⁻¹ ^ 2)) := by
  classical
  let f : ℕ → ℝ := fun p => min (Real.log p / (X * Real.log X))
    (-Real.log (1 - (p : ℝ)⁻¹ ^ 2))
  let H := Nat.primesLE ⌊ρ⌋₊
  let S := Nat.primesLE P
  have hsub : H ⊆ S := Nat.primesLE_mono (Nat.floor_le_of_le hP)
  have hD : 0 < X * Real.log X := mul_pos (by linarith) (Real.log_pos hX)
  have hhead : θ ρ / (X * Real.log X) ≤ ∑ p ∈ H, f p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Finset.sum_div]
    apply sum_le_sum
    intro p hp
    have hpρ : (p : ℝ) ≤ ρ :=
      (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans (Nat.floor_le (by linarith))
    exact PrimeMinCorrectionLower.prime_weight_lower hX hD le_rfl heq.le
      (Nat.mem_primesLE.mp hp).2 hpρ
  have hsets : S \ H = (Ioc ⌊ρ⌋₊ P).filter Nat.Prime := by
    ext p
    simp only [S, H, mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioc]
    tauto
  have htail : (∑ p ∈ S \ H, (1 : ℝ) / (p : ℝ) ^ 2) ≤ ∑ p ∈ S \ H, f p := by
    apply sum_le_sum
    intro p hp
    have hps := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    have hph : ⌊ρ⌋₊ < p := by
      have hnot := (mem_sdiff.mp hp).2
      simp only [H, Nat.mem_primesLE, hps.2, and_true] at hnot
      omega
    have hpρ : ρ < (p : ℝ) := (Nat.floor_lt (by linarith : 0 ≤ ρ)).mp hph
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hps.2.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hps.2.one_lt
    have hmono := second_cutoff_strictMono hρ (by simpa using hp1) hpρ
    rw [heq] at hmono
    have hi : (p : ℝ)⁻¹ ^ 2 < 1 :=
      pow_lt_one₀ (inv_pos.mpr hp0).le ((inv_lt_one₀ hp0).mpr hp1) (by norm_num)
    have ht := Real.log_le_sub_one_of_pos (sub_pos.mpr hi)
    apply le_min
    · apply (div_le_div_iff₀ (sq_pos_of_pos hp0) hD).mpr
      simpa only [one_mul] using hmono.le
    · have hid : (1 : ℝ) / (p : ℝ) ^ 2 = (p : ℝ)⁻¹ ^ 2 := by ring
      rw [hid]
      linarith
  rw [← hsets]
  have hadd := add_le_add hhead htail
  have hsum := sum_sdiff (f := f) hsub
  dsimp only [S] at hsum
  linarith only [hadd, hsum]

end
end D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower
