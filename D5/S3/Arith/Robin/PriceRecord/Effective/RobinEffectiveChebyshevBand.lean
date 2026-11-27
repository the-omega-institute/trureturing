/- GID: D5/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/Effective/RobinEffectiveChebyshevBand
   mirror-E: none(waiver:analytic-arithmetic-inequality)
   anchors: []
   utility: none
   digest: Elementary Chebyshev bounds supply the strict Robin reserve at large square cutoffs. -/

import D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus
import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveFiniteBand
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-! Elementary estimates for the Robin prime-square reserve above the finite bands. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand

open Finset
open D5.S3.Arith.Robin.PriceRecord.Effective.EffectivePrimeSquareSurplus

private theorem log_100000_lt : Real.log 100000 < 12 := by
  rw [show (100000 : ℝ) = (2 * 5)^5 by norm_num, Real.log_pow,
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem theta_lower {t : ℝ} (ht : 100000 ≤ t) :
    (3/5 : ℝ) * t ≤ Chebyshev.theta t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have he2 : Real.exp 2 ≤ (100000 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h := (sq_le_sq₀ (Real.exp_nonneg 1) (by norm_num : (0 : ℝ) ≤ 3)).mpr
      Real.exp_one_lt_three.le
    nlinarith only [h]
  have he1 : Real.exp 1 ≤ (100000 : ℝ) := by linarith [Real.exp_one_lt_three]
  have hs316 : (316 : ℝ) ≤ Real.sqrt 100000 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hmonoS : Real.log t / Real.sqrt t ≤ Real.log 100000 / Real.sqrt 100000 :=
    Real.log_div_sqrt_antitoneOn he2 (he2.trans ht) ht
  have hr : Real.log t / Real.sqrt t ≤ (12/316 : ℝ) :=
    hmonoS.trans ((div_le_div_of_nonneg_right log_100000_lt.le (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs316))
  have hs := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs0).mp hr)
    (show 0 ≤ 2 * Real.sqrt t by positivity)
  have hroot : 2 * Real.sqrt t * Real.log t ≤ (24/316 : ℝ) * t := by
    calc
      _ = Real.log t * (2 * Real.sqrt t) := by ring
      _ ≤ _ := hs
      _ = _ := by rw [show (12/316 : ℝ) * Real.sqrt t * (2 * Real.sqrt t) =
        (24/316 : ℝ) * (Real.sqrt t)^2 by ring, Real.sq_sqrt ht0.le]
  have hmono : Real.log t / t ≤ Real.log 100000 / 100000 :=
    Real.log_div_self_antitoneOn he1 (he1.trans ht) ht
  have hlog : Real.log t ≤ (12/100000 : ℝ) * t := (div_le_iff₀ ht0).mp
    (hmono.trans (div_le_div_of_nonneg_right log_100000_lt.le (by norm_num)))
  have hshift : Real.log (t + 2) ≤ Real.log 2 + Real.log t := by
    have h := Real.log_le_log (show 0 < t + 2 by linarith) (show t + 2 ≤ 2 * t by linarith)
    rwa [Real.log_mul (by norm_num) ht0.ne'] at h
  have hlog2 : Real.log 2 ≤ (7/10/100000 : ℝ) * t := by
    linarith [Real.log_two_lt_d9]
  have hmain := mul_le_mul_of_nonneg_left (show (69/100 : ℝ) ≤ Real.log 2 by
    linarith [Real.log_two_gt_d9]) ht0.le
  have htheta := Chebyshev.theta_ge' ht1
  rw [sub_mul, one_mul] at htheta
  linarith only [htheta, hmain, hshift, hlog, hlog2, hroot, ht0]

private def primesBetween (x y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊x⌋₊

private theorem mem_primesBetween {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {p : ℕ} :
    p ∈ primesBetween x y ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  simp only [primesBetween, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff hx, Nat.le_floor_iff hy]
  constructor
  · rintro ⟨⟨hpy, hpp⟩, hn⟩
    exact ⟨hpp, lt_of_not_ge (fun hpx => hn ⟨hpx, hpp⟩), hpy⟩
  · rintro ⟨hpp, hxp, hpy⟩
    exact ⟨⟨hpy, hpp⟩, fun hn => (not_le_of_gt hxp) hn.1⟩

private theorem sum_primesBetween {x y : ℝ} (hxy : x ≤ y) (f : ℕ → ℝ) :
    ∑ p ∈ primesBetween x y, f p =
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, f p) - ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p :=
  eq_sub_of_add_eq (Finset.sum_sdiff (f := f) (Nat.primesLE_mono (Nat.floor_mono hxy)))

private def logOverSquare (p : ℕ) : ℝ := Real.log (p : ℝ) / (p : ℝ)^2

private theorem band_step {a x k : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hk : 0 < k)
    (hxy : x ≤ k * a) :
    (Chebyshev.theta (k * a) - Chebyshev.theta x) / k^2 ≤
      a^2 * ∑ p ∈ primesBetween x (k * a), logOverSquare p := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
    ← sum_primesBetween hxy (fun p => Real.log (p : ℝ)), Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp, _, hp_le⟩ := (mem_primesBetween hx (mul_nonneg hk.le ha.le)).mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hsq := (sq_le_sq₀ hp0.le (mul_nonneg hk.le ha.le)).mpr hp_le
  unfold logOverSquare
  calc
    _ = a^2 * (Real.log (p : ℝ) / (k * a)^2) := by
      rw [mul_pow]
      field_simp [ha.ne', hk.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hlog (sq_pos_of_pos hp0) hsq) (sq_nonneg _)

/-- Sum three right-endpoint bounds and express the result using the three Chebyshev prefixes. -/
private theorem log_square_prefix {a : ℝ} (ha : 25000 ≤ a) :
    (19/160 : ℝ) / a ≤ ∑ p ∈ primesBetween a (16 * a), logOverSquare p := by
  have ha0 : 0 < a := by linarith
  have h₁ := band_step ha0 ha0.le (by norm_num : (0 : ℝ) < 4) (show a ≤ 4 * a by linarith)
  have h₂ := band_step ha0 (show 0 ≤ 4 * a by positivity) (by norm_num : (0 : ℝ) < 8)
    (show 4 * a ≤ 8 * a by linarith)
  have h₃ := band_step ha0 (show 0 ≤ 8 * a by positivity) (by norm_num : (0 : ℝ) < 16)
    (show 8 * a ≤ 16 * a by linarith)
  have hsplit :
      (∑ p ∈ primesBetween a (4 * a), logOverSquare p) +
        (∑ p ∈ primesBetween (4 * a) (8 * a), logOverSquare p) +
        (∑ p ∈ primesBetween (8 * a) (16 * a), logOverSquare p) =
        ∑ p ∈ primesBetween a (16 * a), logOverSquare p := by
    rw [sum_primesBetween (show a ≤ 4 * a by linarith),
      sum_primesBetween (show 4 * a ≤ 8 * a by linarith),
      sum_primesBetween (show 8 * a ≤ 16 * a by linarith),
      sum_primesBetween (show a ≤ 16 * a by linarith)]
    ring
  have hupper : Chebyshev.theta a ≤ (7/5 : ℝ) * a := by
    refine (Chebyshev.theta_le_log4_mul_x ha0.le).trans (mul_le_mul_of_nonneg_right ?_ ha0.le)
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have h4 := theta_lower (show 100000 ≤ 4 * a by linarith)
  have h8 := theta_lower (show 100000 ≤ 8 * a by linarith)
  have h16 := theta_lower (show 100000 ≤ 16 * a by linarith)
  have hscaled : (19/160 : ℝ) * a ≤
      a^2 * ∑ p ∈ primesBetween a (16 * a), logOverSquare p := by
    rw [← hsplit]
    simp only [mul_add]
    norm_num at h₁ h₂ h₃
    linarith only [h₁, h₂, h₃, hupper, h4, h8, h16]
  calc
    _ = ((19/160 : ℝ) * a) / a^2 := by field_simp [ha0.ne'] <;> ring
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos ha0)).mpr (by simpa only [mul_comm] using hscaled)

private theorem primeBandWeight_lower {p : ℕ} (hp : (51 : ℝ) ≤ p) :
    (49/100 : ℝ) * (1 / (p : ℝ)^2) ≤ primeBandWeight p := by
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  unfold primeBandWeight
  apply (le_div_iff₀ (by positivity : 0 < 2 * ((p : ℝ) - 1) * (p : ℝ)^2)).mpr
  calc
    _ = (49/50) * ((p : ℝ) - 1) := by field_simp [hp0.ne'] <;> ring
    _ ≤ _ := by linarith

private theorem log_10000_le {z : ℝ} (hz : 10000 ≤ z) : 9 ≤ Real.log z := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10000) hz
  rw [show (10000 : ℝ) = (2 * 5)^4 by norm_num, Real.log_pow,
    Real.log_mul (by norm_num) (by norm_num)] at h
  norm_num at h
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

private theorem scale_lower {z : ℝ} (hz : 0 < z) (ha : 25000 ≤ Real.sqrt (2 * z)) :
    Real.sqrt (2 * z) * Real.log (16 * Real.sqrt (2 * z)) ≤ D z := by
  let a := Real.sqrt (2 * z)
  change 25000 ≤ a at ha
  change a * Real.log (16 * a) ≤ Real.sqrt z * Real.log z
  have ha0 : 0 < a := by linarith
  have hal : 9 ≤ Real.log a := by
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^14) (show (2 : ℝ)^14 ≤ a by
      norm_num; linarith)
    rw [Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_gt_d9]
  have hlog16 : Real.log (16 : ℝ) ≤ 14/5 := by
    rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlogz : Real.log z = 2 * Real.log a - Real.log 2 := by
    have h : a^2 = 2 * z := Real.sq_sqrt (by positivity)
    have h' := congrArg Real.log h
    rw [Real.log_pow, Real.log_mul (by norm_num) hz.ne'] at h'
    norm_num at h'
    linarith
  have hs : Real.sqrt (2 : ℝ) ≤ 10/7 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have he : a = Real.sqrt 2 * Real.sqrt z := Real.sqrt_mul (by norm_num) z
  have hlog0 : 0 ≤ Real.log (16 * a) := Real.log_nonneg (by linarith)
  have hc : (10/7 : ℝ) * Real.log (16 * a) ≤ Real.log z := by
    rw [Real.log_mul (by norm_num) ha0.ne', hlogz]
    linarith [Real.log_two_lt_d9]
  calc
    _ = (Real.sqrt 2 * Real.sqrt z) * Real.log (16 * a) :=
      congrArg (fun x : ℝ => x * Real.log (16 * a)) he
    _ = Real.sqrt z * (Real.sqrt 2 * Real.log (16 * a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hs hlog0).trans hc)
      (Real.sqrt_nonneg _)

private theorem reserve_lt_large {z : ℝ} (hz : 1000000 ≤ z) : neededReserve z < 931/16000 := by
  have hz0 : 0 < z := by linarith
  have hlog := log_10000_le (show 10000 ≤ z by linarith)
  have hu0 : 0 < Real.log z := by linarith
  have hs : (1000 : ℝ) ≤ Real.sqrt z := Real.le_sqrt_of_sq_le (by norm_num; exact hz)
  have hi : 1/Real.log z ≤ 1/9 := (div_le_iff₀ hu0).mpr (by linarith)
  have hroot : 2/Real.sqrt z ≤ 2/1000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hc : (1 + 1/Real.log z) / (8*z*Real.sqrt z) ≤ (1+1/9) / (8*1000000*1000) := by
    refine (div_le_div_of_nonneg_right (add_le_add le_rfl hi) (by positivity)).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have h := mul_le_mul hz hs (by norm_num : (0 : ℝ) ≤ 1000) hz0.le
    linarith
  unfold neededReserve
  linarith only [hi, hroot, hc]

/-- For square cutoff at least 25000, the actual prime band pays the explicit Robin reserve. -/
theorem neededReserve_lt_normalizedPrimeBand_of_sqrt_ge {z : ℝ} (hz : 10000 ≤ z)
    (ha : 25000 ≤ Real.sqrt (2 * z)) : neededReserve z < normalizedPrimeBand z := by
  let a := Real.sqrt (2 * z)
  change 25000 ≤ a at ha
  have hz0 : 0 < z := by linarith
  have ha0 : 0 < a := by linarith
  have ha2 : a^2 = 2 * z := Real.sq_sqrt (by positivity)
  have hlarge : 1000000 ≤ z := by
    have h := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 25000) ha0.le).mpr ha
    linarith only [h, ha2]
  have haz : 16 * a ≤ z := by
    have h := mul_le_mul_of_nonneg_right (show 32 ≤ a by linarith) ha0.le
    nlinarith only [h, ha2]
  let S := primesBetween a (16 * a)
  have hdata {p : ℕ} (hp : p ∈ S) : p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ 16 * a :=
    (mem_primesBetween ha0.le (by positivity)).mp hp
  have hsub : S ⊆ primeBand z := by
    intro p hp
    obtain ⟨hpp, hpa, hp16⟩ := hdata hp
    have hsq := (sq_lt_sq₀ ha0.le (Nat.cast_nonneg p)).mpr hpa
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor (hp16.trans haz), hpp⟩,
      by simpa only [ha2] using hsq⟩
  have hsum : (∑ p ∈ S, primeBandWeight p) ≤ ∑ p ∈ primeBand z, primeBandWeight p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hpp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp1 : 0 < (p : ℝ) - 1 := by linarith
    unfold primeBandWeight
    exact div_nonneg (sub_nonneg.mpr hp2) (by positivity)
  have hl0 : 0 ≤ Real.log (16 * a) := Real.log_nonneg (by linarith)
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (49/100 : ℝ) * logOverSquare p ≤ Real.log (16 * a) * primeBandWeight p := by
    obtain ⟨_, hpa, hpb⟩ := hdata hp
    have hp0 : 0 < (p : ℝ) := ha0.trans hpa
    have hpl := Real.log_le_log hp0 hpb
    have hweight := primeBandWeight_lower (p := p) (by linarith)
    calc
      _ = Real.log (p : ℝ) * ((49/100 : ℝ) * (1 / (p : ℝ)^2)) := by unfold logOverSquare; ring
      _ ≤ Real.log (16 * a) * ((49/100 : ℝ) * (1 / (p : ℝ)^2)) :=
        mul_le_mul_of_nonneg_right hpl (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight hl0
  have hweighted := Finset.sum_le_sum hpoint
  simp only [← Finset.mul_sum] at hweighted
  have hpref := mul_le_mul_of_nonneg_left (log_square_prefix ha) (by norm_num : (0 : ℝ) ≤ 49/100)
  have hlo := mul_le_mul_of_nonneg_left (hpref.trans hweighted) ha0.le
  have hcert : (931/16000 : ℝ) ≤ (a * Real.log (16 * a)) * ∑ p ∈ S, primeBandWeight p := by
    calc
      _ = a * ((49/100 : ℝ) * ((19/160 : ℝ) / a)) := by
        field_simp [ha0.ne'] <;> ring
      _ ≤ _ := by simpa only [mul_assoc] using hlo
  have hsum0 : 0 ≤ ∑ p ∈ S, primeBandWeight p := by
    apply Finset.sum_nonneg
    intro p hp
    refine (show 0 ≤ (49/100 : ℝ) * (1 / (p : ℝ)^2) by positivity).trans
      (primeBandWeight_lower (p := p) ?_)
    linarith [(hdata hp).2.1]
  have hD : 0 ≤ D z := by unfold D; exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith))
  unfold normalizedPrimeBand
  exact (reserve_lt_large hlarge).trans_le (hcert.trans
    (mul_le_mul (scale_lower hz0 ha) hsum hsum0 hD))

/-- The finite certificate and the Chebyshev supplier cover every real cutoff
at least ten thousand, without any zero-location hypothesis. -/
theorem neededReserve_lt_normalizedPrimeBand {z : ℝ} (hz : 10000 ≤ z) :
    neededReserve z < normalizedPrimeBand z := by
  by_cases ha : Real.sqrt (2 * z) ≤ 25000
  · exact neededReserve_lt_normalizedPrimeBand_of_sqrt_le hz ha
  · exact neededReserve_lt_normalizedPrimeBand_of_sqrt_ge hz (le_of_not_ge ha)

end D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveChebyshevBand
