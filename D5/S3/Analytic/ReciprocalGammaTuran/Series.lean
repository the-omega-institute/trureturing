/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed, mathlib/module/Mathlib.Analysis.Normed.Ring.InfiniteSum, mathlib/module/Mathlib.RingTheory.PowerSeries.Derivative, mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Analytic.OfScalars, mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Entire reciprocal Gamma series, exact Turanian coefficients, and differential coefficient recurrence. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Defs
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open scoped BigOperators
open Filter Topology Finset
open D5.S3.Analytic.ReciprocalGammaTuran.Defs

namespace D5.S3.Analytic.ReciprocalGammaTuran.Series

/-- The entire reciprocal Gamma series on the real axis. -/
def F (b x : ℝ) : ℝ := ∑' n : ℕ, rgamma ((n : ℝ) + b) * x ^ n

/-- The formal series for an arbitrary coefficient sequence. -/
def formalSeries (g : ℕ → ℝ) (b : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => g n * rgamma ((n : ℝ) + b))

/-- The formal boundary Turanian. -/
def boundarySeries (t : ℝ) : PowerSeries ℝ :=
  formalSeries (fun _ => 1) 0 ^ 2 -
    formalSeries (fun _ => 1) (-t) * formalSeries (fun _ => 1) t

/-- Boundary coefficients in the ordinary power basis. -/
def d (t : ℝ) (m : ℕ) : ℝ := PowerSeries.coeff m (boundarySeries t)

private lemma rgamma_shift (x : ℝ) : x * rgamma (x + 1) = rgamma x := by
  by_cases hx : x = 0
  · subst x; simp [rgamma, Real.Gamma_zero]
  · simp only [rgamma, Real.Gamma_add_one hx, mul_inv_rev]
    calc
      _ = (x * x⁻¹) * (Real.Gamma x)⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hx, one_mul]

private lemma rgamma_succ (b : ℝ) (n : ℕ) (h : (n : ℝ) + b ≠ 0) :
    rgamma ((n + 1 : ℕ) + b) = ((n : ℝ) + b)⁻¹ * rgamma ((n : ℝ) + b) := by
  have hh := rgamma_shift ((n : ℝ) + b)
  have he : ((n + 1 : ℕ) : ℝ) + b = ((n : ℝ) + b) + 1 := by push_cast; ring
  rw [he, ← hh]
  simp [h]

private lemma summable_norm_series (b x : ℝ) :
    Summable (fun n : ℕ => ‖rgamma ((n : ℝ) + b) * x ^ n‖) := by
  have hlim : Tendsto (fun n : ℕ => ‖((n : ℝ) + b)⁻¹ * x‖) atTop (𝓝 0) := by
    have h := (tendsto_mul_add_inv_atTop_nhds_zero 1 b one_ne_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa using (h.mul_const x).norm
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) + b :=
    (tendsto_atTop_add_const_right atTop b tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2), hpos] with n hn hp
  simp only [norm_norm]
  rw [rgamma_succ b n hp.ne', pow_succ]
  have he : ((↑n + b)⁻¹ * rgamma (↑n + b)) * (x ^ n * x) =
      ((↑n + b)⁻¹ * x) * (rgamma (↑n + b) * x ^ n) := by ring
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- The reciprocal Gamma series has infinite convergence radius. -/
theorem entire_series (b : ℝ) :
    HasFPowerSeriesOnBall (F b)
      (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => rgamma ((n : ℝ) + b))) 0 ⊤ := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => rgamma ((n : ℝ) + b))
  have hr : p.radius = ⊤ := by
    apply p.radius_eq_top_of_summable_norm
    intro R
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      Real.norm_of_nonneg R.coe_nonneg] using summable_norm_series b (R : ℝ)
  refine { r_le := hr.ge
           r_pos := by simp
           hasSum := ?_ }
  intro y hy
  simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, F]
    using (summable_norm_series b y).of_norm.hasSum

/-- The defining series converges at every real argument. -/
theorem hasSum_series (b x : ℝ) :
    HasSum (fun n : ℕ => rgamma ((n : ℝ) + b) * x ^ n) (F b x) := by
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using
    (entire_series b).hasSum (show x ∈ Metric.eball (0 : ℝ) ⊤ from by simp)

/-- The pinned finite sum is exactly the coefficient of the formal products. -/
theorem coeff_mul (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) :
    PowerSeries.coeff m
      (formalSeries g (μ + α) * formalSeries g (μ + β) -
        formalSeries g μ * formalSeries g (μ + α + β)) = turanCoeff g μ α β m := by
  simp only [map_sub, PowerSeries.coeff_mul, formalSeries, PowerSeries.coeff_mk,
    ← Finset.sum_sub_distrib, turanCoeff]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    (g i * rgamma (i + (μ + α)) * (g j * rgamma (j + (μ + β)))) -
    (g i * rgamma (i + μ) * (g j * rgamma (j + (μ + α + β))))) m]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  simp only [add_assoc]
  ring

/-- The boundary specialization identifies the pinned coefficients with `d`. -/
theorem turanCoeff_one_boundary (t : ℝ) (m : ℕ) :
    turanCoeff (fun _ => 1) (-t) t t m = d t m := by
  have h := coeff_mul (fun _ => (1 : ℝ)) (-t) t t m
  simpa [d, boundarySeries, pow_two] using h.symm

/-- The real Cauchy product has the same coefficients as the formal product. -/
theorem hasSum_turanCoeff (μ α β x : ℝ) :
    HasSum (fun m : ℕ => turanCoeff (fun _ => 1) μ α β m * x ^ m)
      (F (μ + α) x * F (μ + β) x - F μ x * F (μ + α + β) x) := by
  have h₁ := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_series (μ + α) x) (summable_norm_series (μ + β) x)
  have h₂ := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_series μ x) (summable_norm_series (μ + α + β) x)
  change HasSum _ ((∑' n : ℕ, rgamma (n + (μ + α)) * x ^ n) *
    (∑' n : ℕ, rgamma (n + (μ + β)) * x ^ n) -
    (∑' n : ℕ, rgamma (n + μ) * x ^ n) *
    (∑' n : ℕ, rgamma (n + (μ + α + β)) * x ^ n))
  convert h₁.sub h₂ using 1
  ext m
  simp only [turanCoeff, one_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.cast_sub hkm]
  rw [show x ^ m = x ^ k * x ^ (m-k) by rw [← pow_add, Nat.add_sub_of_le hkm]]
  simp only [add_assoc]
  ring

private lemma coeff_deriv (b : ℝ) (n : ℕ) :
    rgamma (((n + 1 : ℕ) : ℝ) + b) * ((n : ℝ) + 1) =
      rgamma ((n : ℝ) + b) + (1 - b) * rgamma ((n : ℝ) + (b + 1)) := by
  have h := rgamma_shift ((n : ℝ) + b)
  have h₁ : ((n + 1 : ℕ) : ℝ) + b = (n : ℝ) + b + 1 := by push_cast; ring
  rw [h₁]
  rw [show (n : ℝ) + (b + 1) = (n : ℝ) + b + 1 by ring]
  nlinarith

private lemma F_tail (b x : ℝ) :
    F b x = rgamma b + ∑' n : ℕ, rgamma (((n+1 : ℕ) : ℝ) + b) * x ^ (n+1) := by
  simpa [F] using (hasSum_series b x).summable.tsum_eq_zero_add

private lemma F_shift (b x : ℝ) : F b x = rgamma b + x * F (b+1) x := by
  rw [F_tail, F, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show (n : ℝ) + 1 + b = (n : ℝ) + (b + 1) by ring]
  ring

private lemma F_one (x : ℝ) : F 1 x = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp only [F]
  apply tsum_congr
  intro n
  simp [rgamma, Real.Gamma_nat_eq_factorial, div_eq_mul_inv, mul_comm]

/-- The zero parameter series is the exponential series multiplied by its argument. -/
theorem F_zero (x : ℝ) : F 0 x = x * Real.exp x := by
  have h := rgamma_neg_nat 0
  norm_num at h
  rw [F_shift, zero_add, h, zero_add, F_one]

/-- Termwise differentiation holds at every real argument. -/
theorem hasDerivAt_F (b x : ℝ) :
    HasDerivAt (F b) (F b x + (1-b) * F (b+1) x) x := by
  let R : ℝ := |x| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let a : ℕ → ℝ := fun n => rgamma ((n : ℝ) + b) + (1-b) * rgamma ((n : ℝ) + (b+1))
  let g : ℕ → ℝ → ℝ := fun n y => rgamma (((n+1 : ℕ) : ℝ) + b) * y ^ (n+1)
  let g' : ℕ → ℝ → ℝ := fun n y => a n * y ^ n
  let u : ℕ → ℝ := fun n =>
    ‖rgamma ((n : ℝ) + b) * R ^ n‖ + ‖1-b‖ * ‖rgamma ((n : ℝ) + (b+1)) * R ^ n‖
  have hu : Summable u := (summable_norm_series b R).add
    ((summable_norm_series (b+1) R).mul_left _)
  have hd : ∀ n y, y ∈ Set.Ioo (-R) R → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have h := ((hasDerivAt_id y).pow (n+1)).const_mul (rgamma (((n+1 : ℕ) : ℝ) + b))
    simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, ← mul_assoc,
      Nat.cast_add, Nat.cast_one] at h
    have hc := coeff_deriv b n
    simp only [Nat.cast_add, Nat.cast_one] at hc
    rw [hc] at h
    simpa only [g, g', a, Nat.cast_add, Nat.cast_one] using h
  have hb : ∀ n y, y ∈ Set.Ioo (-R) R → ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyR : ‖y‖ ≤ R := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hy.1], hy.2.le⟩
    have hp := pow_le_pow_left₀ (norm_nonneg y) hyR n
    simp only [g', u, a]
    calc
      _ ≤ (‖rgamma ((n : ℝ) + b)‖ + ‖1-b‖ * ‖rgamma ((n : ℝ) + (b+1))‖) * ‖y‖ ^ n := by
        rw [norm_mul, norm_pow]
        have hh := norm_add_le (rgamma ((n : ℝ) + b))
          ((1-b) * rgamma ((n : ℝ) + (b+1)))
        rw [norm_mul] at hh
        exact mul_le_mul_of_nonneg_right hh (by positivity)
      _ ≤ (‖rgamma ((n : ℝ) + b)‖ + ‖1-b‖ * ‖rgamma ((n : ℝ) + (b+1))‖) * R ^ n :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by simp [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hR]; ring
  have h0 : (0 : ℝ) ∈ Set.Ioo (-R) R := ⟨by linarith, hR⟩
  have hx : x ∈ Set.Ioo (-R) R := by
    dsimp [R]; constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have hg0 : Summable (fun n => g n 0) := by simp [g]
  have ht := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-R) R).isPreconnected hd hb h0 hg0 hx
  have he : (fun y => rgamma b + ∑' n, g n y) = F b := by
    ext y; exact (F_tail b y).symm
  have h := ht.const_add (rgamma b)
  rw [he] at h
  convert h using 1
  dsimp [g', a, F]
  simp_rw [add_mul, mul_assoc]
  rw [(hasSum_series b x).summable.tsum_add
    ((hasSum_series (b+1) x).summable.mul_left (1-b)), tsum_mul_left]

/-- The inhomogeneous differential equation of the entire reciprocal Gamma series. -/
theorem differential_recurrence (b x : ℝ) :
    x * deriv (F b) x = (x+1-b) * F b x + (b-1) * rgamma b := by
  rw [(hasDerivAt_F b x).deriv]
  rw [F_shift b x]
  ring

/-- The inhomogeneous differential identity in the formal power series ring. -/
theorem formal_recurrence (b : ℝ) :
    PowerSeries.X * PowerSeries.derivative (formalSeries (fun _ => 1) b) =
      (PowerSeries.X + PowerSeries.C (1 - b)) * formalSeries (fun _ => 1) b +
        PowerSeries.C ((b - 1) * rgamma b) := by
  ext n
  cases n with
  | zero => simp [formalSeries]; ring
  | succ n =>
    simp only [add_mul, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, formalSeries,
      PowerSeries.coeff_mk, one_mul, PowerSeries.coeff_C, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ite_false, add_zero, Nat.cast_add, Nat.cast_one]
    have h := rgamma_shift ((n : ℝ) + b)
    have he : (n : ℝ) + b + 1 = (n : ℝ) + 1 + b := by ring
    rw [he] at h
    nlinarith

/-- The forcing coefficients of the boundary differential identity. -/
def r (t : ℝ) (m : ℕ) : ℝ :=
  (t + 1) * rgamma (-t) * rgamma ((m : ℝ) + t) +
    (1 - t) * rgamma t * rgamma ((m : ℝ) - t)

/-- The formal differential identity for the boundary Turanian. -/
theorem boundary_recurrence (t : ℝ) :
    PowerSeries.X * PowerSeries.derivative (boundarySeries t) =
      2 * (PowerSeries.X + 1) * boundarySeries t +
        PowerSeries.C ((t + 1) * rgamma (-t)) * formalSeries (fun _ => 1) t +
        PowerSeries.C ((1 - t) * rgamma t) * formalSeries (fun _ => 1) (-t) := by
  have h₀ := formal_recurrence 0
  have h₁ := formal_recurrence (-t)
  have h₂ := formal_recurrence t
  simp only [sub_zero, rgamma, Real.Gamma_zero, inv_zero, mul_zero, map_zero,
    add_zero, map_one] at h₀
  simp only [sub_neg_eq_add] at h₁
  simp only [boundarySeries, pow_two, map_sub, PowerSeries.derivative.leibniz,
    smul_eq_mul]
  calc
    _ = 2 * formalSeries (fun _ => 1) 0 *
          (PowerSeries.X * PowerSeries.derivative (formalSeries (fun _ => 1) 0)) -
        formalSeries (fun _ => 1) (-t) *
          (PowerSeries.X * PowerSeries.derivative (formalSeries (fun _ => 1) t)) -
        formalSeries (fun _ => 1) t *
          (PowerSeries.X * PowerSeries.derivative (formalSeries (fun _ => 1) (-t))) := by ring
    _ = _ := by
      rw [h₀, h₁, h₂]
      simp only [map_sub, map_mul, map_add, map_neg, map_one]
      ring

/-- The boundary coefficients satisfy the inhomogeneous first order recurrence. -/
theorem coefficient_recurrence (t : ℝ) (m : ℕ) (hm : 3 ≤ m) :
    ((m : ℝ) - 2) * d t m = 2 * d t (m - 1) + r t m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
  have h := congrArg (PowerSeries.coeff (1 + n)) (boundary_recurrence t)
  simp only [mul_add, mul_assoc, add_mul, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_ofNat_mul, mul_one, add_comm 1 n, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative, mul_one, formalSeries,
    PowerSeries.coeff_mk, one_mul] at h
  simp only [d, r, Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_one, sub_eq_add_neg] at h ⊢
  simp only [add_comm 1 n, add_comm (1 : ℝ) (n : ℝ)] at h ⊢
  nlinarith [h]

end D5.S3.Analytic.ReciprocalGammaTuran.Series
