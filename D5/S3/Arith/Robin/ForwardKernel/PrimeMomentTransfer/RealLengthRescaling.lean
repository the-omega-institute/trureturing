/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthRescaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact interval rescaling and floor geometry control real-length variance errors. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.LogWindow
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.UniformRates

/-! Exact endpoint rescaling and uniform variance control for natural floors of real lengths. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_delta_rescale (H K a b x : ℝ) (hK : 0 < K) :
    Delta H a b x = Delta K ((H / K) * a) ((H / K) * b) x := by
  have he (c : ℝ) : H / K * c * K = c * H := by field_simp [hK.ne']
  simp only [Delta, he]
  congr 1
  field_simp [hK.ne']

private theorem p_z_rescale (N H K a b x : ℝ) (hL : 0 < Real.log N)
    (hH : 0 < H) (hK : 0 < K) :
    Z H a b x N = Real.sqrt (K / H) * Z K ((H / K) * a) ((H / K) * b) x N := by
  have hsH : Real.sqrt H ≠ 0 := (Real.sqrt_pos.2 hH).ne'
  have hsK : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  have hsL : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  unfold Z
  rw [p_delta_rescale H K a b x hK, Real.sqrt_div hK.le,
    Real.sqrt_mul hH.le, Real.sqrt_mul hK.le]
  field_simp [hsH, hsK, hsL]

/-- Exact endpoint rescaling changes a normalized mixed moment by its normalizer ratio. -/
theorem moment_rescale (N H K : ℝ) (k : ℕ) (a b : Fin k → ℝ) (w : ℝ → ℝ)
    (_hN : 0 < N) (hL : 0 < Real.log N) (hH : 0 < H) (hK : 0 < K) :
    weightedMoment N H a b w = (K / H) ^ ((k : ℝ) / 2) *
      weightedMoment N K (fun i => (H / K) * a i) (fun i => (H / K) * b i) w := by
  have hp : Real.sqrt (K / H) ^ k = (K / H) ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hf (x : ℝ) : w (x / N) * (∏ i, Z H (a i) (b i) x N) =
      (K / H) ^ ((k : ℝ) / 2) *
        (w (x / N) * ∏ i, Z K ((H / K) * a i) ((H / K) * b i) x N) := by
    simp only [p_z_rescale N H K _ _ _ hL hH hK, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hp]
    ring
  unfold weightedMoment
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem p_sigma_rescale (r a b c d : ℝ) (hr : 0 ≤ r) :
    sigma (r * a) (r * b) (r * c) (r * d) = r * sigma a b c d := by
  unfold sigma
  rw [← mul_min_of_nonneg b d hr, ← mul_max_of_nonneg a c hr,
    ← mul_sub, mul_max_of_nonneg 0 (min b d - max a c) hr, mul_zero]

/-- The fourth overlap pairing is homogeneous of degree two. -/
theorem w4_rescale (r : ℝ) (a b : Fin 4 → ℝ) (hr : 0 ≤ r) :
    W4 (fun i => r * a i) (fun i => r * b i) = r ^ 2 * W4 a b := by
  simp only [W4, p_sigma_rescale r _ _ _ _ hr]
  ring

/-- A rescaling by at most two preserves admissibility in the doubled window. -/
theorem rescaled_admissible (M r : ℝ) (k : ℕ) (a b : Fin k → ℝ)
    (hr : 0 ≤ r) (hr2 : r ≤ 2) (hab : admissible M a b) :
    admissible (2 * M) (fun i => r * a i) (fun i => r * b i) := by
  intro i
  obtain ⟨ha, habi, hb⟩ := hab i
  have hM : 0 ≤ M := ha.trans (habi.trans hb)
  exact ⟨mul_nonneg hr ha, mul_le_mul_of_nonneg_left habi hr,
    (mul_le_mul_of_nonneg_left hb hr).trans (mul_le_mul_of_nonneg_right hr2 hM)⟩

/-- Taking the natural floor preserves a polynomial band after halving its lower exponent. -/
theorem floor_range (α β : ℝ) (hα : 0 < α) (_hαβ : α < β) (_hβ : β < 1) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, N ^ α ≤ H → H ≤ N ^ β →
      1 ≤ ⌊H⌋₊ ∧ N ^ (α / 2) ≤ (⌊H⌋₊ : ℝ) ∧ (⌊H⌋₊ : ℝ) ≤ N ^ β ∧
      1 ≤ H / (⌊H⌋₊ : ℝ) ∧ H / (⌊H⌋₊ : ℝ) ≤ 2 := by
  filter_upwards [(tendsto_rpow_atTop (half_pos hα)).eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with N hpow hN H hlo hhi
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have heq : N ^ α = (N ^ (α / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    norm_num
  have hH : 0 ≤ H := (Real.rpow_nonneg hN0.le α).trans hlo
  have hfloor := Nat.floor_le hH
  have hlt := Nat.lt_floor_add_one H
  have hlow : N ^ (α / 2) ≤ (⌊H⌋₊ : ℝ) := by
    rw [heq] at hlo
    nlinarith
  have hK1 : (1 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by linarith
  have hK0 : 0 < (⌊H⌋₊ : ℝ) := zero_lt_one.trans_le hK1
  refine ⟨by exact_mod_cast hK1, hlow, hfloor.trans hhi,
    (one_le_div hK0).2 hfloor, (div_le_iff₀ hK0).2 ?_⟩
  linarith

private theorem p_floor_variance_bound (N H : ℝ) (hN : 2 ≤ N)
    (hK : 1 ≤ (⌊H⌋₊ : ℝ)) (hHN : H ≤ N) :
    |(kappa N (⌊H⌋₊ : ℝ)) ^ 2 - (kappa N H) ^ 2| ≤
      2 / ((⌊H⌋₊ : ℝ) * Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < (⌊H⌋₊ : ℝ) := zero_lt_one.trans_le hK
  have hH0 : 0 < H := Nat.pos_of_floor_pos (by exact_mod_cast hK0)
  have hKH := Nat.floor_le hH0.le
  have hH1 : 1 ≤ H := hK.trans hKH
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hA := variance_ratio_bounds N (⌊H⌋₊ : ℝ) hN hK (hKH.trans hHN)
  have hB := variance_ratio_bounds N H hN hH1 hHN
  have hlog0 : 0 ≤ Real.log H - Real.log (⌊H⌋₊ : ℝ) :=
    sub_nonneg.mpr (Real.strictMonoOn_log.monotoneOn hK0 hH0 hKH)
  have hlog : Real.log H - Real.log (⌊H⌋₊ : ℝ) ≤ 1 / (⌊H⌋₊ : ℝ) := by
    rw [← Real.log_div hH0.ne' hK0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hH0 hK0)).trans ?_
    apply (le_div_iff₀ hK0).2
    have he : (H / (⌊H⌋₊ : ℝ) - 1) * (⌊H⌋₊ : ℝ) = H - (⌊H⌋₊ : ℝ) := by
      field_simp
    rw [he]
    linarith [Nat.lt_floor_add_one H]
  have hd : kappa N (⌊H⌋₊ : ℝ) - kappa N H =
      (Real.log H - Real.log (⌊H⌋₊ : ℝ)) / Real.log N := by
    simp only [kappa, Real.log_div hN0.ne' hK0.ne', Real.log_div hN0.ne' hH0.ne']
    ring
  have hd0 : 0 ≤ kappa N (⌊H⌋₊ : ℝ) - kappa N H := by
    rw [hd]
    exact div_nonneg hlog0 hL.le
  have hdle : kappa N (⌊H⌋₊ : ℝ) - kappa N H ≤
      1 / ((⌊H⌋₊ : ℝ) * Real.log N) := by
    rw [hd, ← div_div]
    exact div_le_div_of_nonneg_right hlog hL.le
  have hs0 : 0 ≤ kappa N (⌊H⌋₊ : ℝ) + kappa N H := add_nonneg hA.1 hB.1
  have hs2 : kappa N (⌊H⌋₊ : ℝ) + kappa N H ≤ 2 := by linarith [hA.2, hB.2]
  rw [show (kappa N (⌊H⌋₊ : ℝ)) ^ 2 - (kappa N H) ^ 2 =
    (kappa N (⌊H⌋₊ : ℝ) - kappa N H) *
      (kappa N (⌊H⌋₊ : ℝ) + kappa N H) by ring,
    abs_of_nonneg (mul_nonneg hd0 hs0)]
  calc
    _ ≤ (1 / ((⌊H⌋₊ : ℝ) * Real.log N)) * 2 :=
      mul_le_mul hdle hs2 hs0 (by positivity)
    _ = _ := by ring

/-- Squared variance ratios at a real length and its natural floor differ uniformly by o(1). -/
theorem floor_variance_rate (α β δ : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ : β < 1) (hδ : 0 < δ) :
    ∀ᶠ N : ℝ in atTop, ∀ H : ℝ, N ^ α ≤ H → H ≤ N ^ β →
      |(kappa N (⌊H⌋₊ : ℝ)) ^ 2 - (kappa N H) ^ 2| ≤ δ := by
  filter_upwards [floor_range α β hα hαβ hβ,
    range_geometry α β 1 hα hβ zero_lt_one,
    inverse_log_rate (δ / 2) (half_pos hδ)] with N hfloor hgeom hsmall H hlo hhi
  have hK : (1 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by
    exact_mod_cast (hfloor H hlo hhi).1
  have hL : 0 < Real.log N := zero_lt_one.trans_le hgeom.2.1
  have hden : Real.log N ≤ (⌊H⌋₊ : ℝ) * Real.log N :=
    le_mul_of_one_le_left hL.le hK
  calc
    _ ≤ 2 / ((⌊H⌋₊ : ℝ) * Real.log N) :=
      p_floor_variance_bound N H hgeom.1 hK (hgeom.2.2 H hlo hhi).2.1
    _ ≤ 2 / Real.log N := div_le_div_of_nonneg_left (by norm_num) hL hden
    _ = 2 * (1 / Real.log N) := by ring
    _ ≤ δ := by linarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
