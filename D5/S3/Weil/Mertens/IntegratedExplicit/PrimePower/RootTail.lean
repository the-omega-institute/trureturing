/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Root cutoffs transport the complete Chebyshev tail. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection

/-! Root substitution and absolute Fubini preserve the centered tail, while Costa Pereira's
inequalities control the part beyond the square and cube cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q psiErrorKernel)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail tail_eq diff_integrable)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private lemma weighted_tail_transport {f : ℝ → ℝ} {r y : ℝ}
    (hr : 1 < r) (hy : 0 < y) (hf : IntegrableOn f (Ioi y)) :
    IntegrableOn (fun s => s ^ (-r) * (∫ t in Ioi s, f t)) (Ioi y) ∧
    (∫ s in Ioi y, f s * s ^ (1 - r)) =
      y ^ (1 - r) * (∫ s in Ioi y, f s) -
        (r - 1) * (∫ s in Ioi y, s ^ (-r) * (∫ t in Ioi s, f t)) := by
  let triangle (s t : ℝ) :=
    {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => p.1 ^ (-r) * f p.2) (s, t)
  have hp := integrableOn_Ioi_rpow_of_lt (show -r < -1 by linarith) hy
  have htri : Integrable (Function.uncurry triangle)
      ((volume.restrict (Ioi y)).prod (volume.restrict (Ioi y))) :=
    (hp.mul_prod hf).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hright (s : ℝ) (hs : y < s) :
      (∫ t in Ioi y, triangle s t) = s ^ (-r) * (∫ t in Ioi s, f t) := by
    have heq : triangle s = (Ioi s).indicator (fun t => s ^ (-r) * f t) := by
      ext t
      rfl
    rw [heq, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hs.le), integral_const_mul]
  have hleft (t : ℝ) (ht : y < t) :
      (∫ s in Ioi y, triangle s t) = f t * ((t ^ (1 - r) - y ^ (1 - r)) / (1 - r)) := by
    have heq : (fun s => triangle s t) = (Iio t).indicator (fun s => s ^ (-r) * f t) := by
      ext s
      rfl
    rw [heq, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Ioi_inter_Iio, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.le, integral_rpow
        (Or.inr ⟨by linarith, by rw [uIcc_of_le ht.le]; exact fun h => hy.not_ge h.1⟩)]
    rw [show -r + 1 = 1 - r by ring]
    ring
  have hi : IntegrableOn (fun s => s ^ (-r) * (∫ t in Ioi s, f t)) (Ioi y) := by
    apply htri.integral_prod_left.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hright s hs
  have hweighted : IntegrableOn (fun t => f t * t ^ (1 - r)) (Ioi y) := by
    apply (hf.norm.mul_const (y ^ (1 - r))).mono' ?_ ?_
    · exact (hf.aestronglyMeasurable.mul (by fun_prop :
        Measurable (fun t : ℝ => t ^ (1 - r))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change ‖f t * t ^ (1 - r)‖ ≤ ‖f t‖ * y ^ (1 - r)
      rw [norm_mul, Real.norm_eq_abs (t ^ (1 - r)),
        abs_of_nonneg (Real.rpow_nonneg (hy.trans ht).le _)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy ht.le (by linarith))
        (norm_nonneg _)
  have hswap := integral_integral_swap htri
  rw [setIntegral_congr_fun measurableSet_Ioi hright,
    setIntegral_congr_fun measurableSet_Ioi hleft] at hswap
  have hsplit : (∫ t in Ioi y, f t * ((t ^ (1 - r) - y ^ (1 - r)) / (1 - r))) =
      ((∫ t in Ioi y, f t * t ^ (1 - r)) - (∫ t in Ioi y, f t * y ^ (1 - r))) / (1 - r) := by
    calc
      _ = ∫ t in Ioi y, (f t * t ^ (1 - r) - f t * y ^ (1 - r)) / (1 - r) :=
        setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
      _ = _ := by
        rw [integral_div, integral_sub (f := fun t => f t * t ^ (1 - r))
          (g := fun t => f t * y ^ (1 - r)) hweighted (hf.mul_const _)]
  rw [hsplit, integral_mul_const] at hswap
  refine ⟨hi, ?_⟩
  have h := (eq_div_iff (show 1 - r ≠ 0 by linarith)).mp hswap
  linear_combination -h

/-- The normalized centered root-cutoff integral in terms of the complete Chebyshev tail. -/
theorem centered_root_tail {r x : ℝ} (hr : 1 < r) (hx : 1 ≤ x) :
    let y := x ^ r⁻¹
    Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2) =
      r * Real.sqrt x *
        (Q y * y ^ (1 - r) - (r - 1) * (∫ s in Ioi y, s ^ (-r) * Q s)) := by
  dsimp only
  let y := x ^ r⁻¹
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hr0 : 0 < r := by linarith
  have hy : 1 ≤ y := Real.one_le_rpow hx (inv_nonneg.mpr hr0.le)
  have htransport := (weighted_tail_transport hr (zero_lt_one.trans_le hy)
    (chebyshev_error_kernel_integrable.mono_set (Ioi_subset_Ioi hy))).2
  change (∫ s in Ioi y, psiErrorKernel s * s ^ (1 - r)) =
    y ^ (1 - r) * Q y - (r - 1) * (∫ s in Ioi y, s ^ (-r) * Q s) at htransport
  let g (t : ℝ) := (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2
  have hsub := integral_comp_rpow_Ioi_of_pos' (g := g) hr0 hx0.le
  have heq (s : ℝ) (hs : s ∈ Ioi y) :
      (r * s ^ (r - 1)) • g (s ^ r) = r * (psiErrorKernel s * s ^ (1 - r)) := by
    have hs0 : 0 < s := zero_lt_one.trans (hy.trans_lt hs)
    have hroot : (s ^ r) ^ r⁻¹ = s := by
      rw [← Real.rpow_mul hs0.le, mul_inv_cancel₀ hr0.ne', Real.rpow_one]
    have hpow : (s ^ r) ^ (2 : ℕ) = s ^ (2 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
      norm_num
      ring_nf
    have hfactor : s ^ (r - 1) / s ^ (2 * r) = s ^ (1 - r) / s ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      simp only [Nat.cast_ofNat, ← Real.rpow_sub hs0]
      congr 1
      ring
    dsimp only [smul_eq_mul, g]
    rw [hroot, hpow, psiErrorKernel]
    calc
      _ = r * ((Chebyshev.psi s - s) * (s ^ (r - 1) / s ^ (2 * r))) := by ring
      _ = _ := by rw [hfactor]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, htransport] at hsub
  change Real.sqrt x * (∫ t in Ioi x, g t) =
    r * Real.sqrt x * (Q y * y ^ (1 - r) - (r - 1) * (∫ s in Ioi y, s ^ (-r) * Q s))
  rw [← hsub]
  ring

private lemma root_kernel_integrable {p x : ℝ} (hp : p < 1) (hx : 0 < x) :
    IntegrableOn (fun t => Chebyshev.psi (t ^ p) / t ^ 2) (Ioi x) := by
  apply ((integrableOn_Ioi_rpow_of_lt (a := p - 2) (by linarith) hx).const_mul
    (Real.log 4 + 4)).mono'
  · exact ((Chebyshev.psi_mono.measurable.comp (by fun_prop)).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hx.trans ht
    change ‖Chebyshev.psi (t ^ p) / t ^ 2‖ ≤ (Real.log 4 + 4) * t ^ (p - 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Chebyshev.psi_nonneg _) (sq_nonneg _)),
      Real.rpow_sub ht0, Real.rpow_two, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (Chebyshev.psi_le_const_mul_self (by positivity)) (sq_nonneg _)

/-- After isolating square and cube cutoffs, Costa Pereira's upper remainder integrates
to a fifth-root majorant. -/
theorem root_cutoff_remainder {x : ℝ} (hx : 1 ≤ x) :
    let E := Q x - primeTail x -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2)
    0 ≤ E ∧ Real.sqrt x * E ≤ (Real.log 4 + 4) * (5 / 4) * x ^ (-(3 / 10) : ℝ) := by
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h2 := root_kernel_integrable (p := (2 : ℝ)⁻¹) (by norm_num) hx0
  have h3 := root_kernel_integrable (p := (3 : ℝ)⁻¹) (by norm_num) hx0
  have hd := diff_integrable.mono_set (Ioi_subset_Ioi hx)
  let rem (t : ℝ) := (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 -
    Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2 - Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2
  have hi : IntegrableOn rem (Ioi x) := (hd.sub h2).sub h3
  have he : Q x - primeTail x - (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) = ∫ t in Ioi x, rem t := by
    rw [tail_eq hx]
    exact (congrArg (· - (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2))
      (integral_sub hd h2).symm).trans (integral_sub (hd.sub h2) h3).symm
  rw [he]
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have hl := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi (hx0.trans ht).le
    have hnonneg := Chebyshev.psi_nonneg (t ^ (7 : ℝ)⁻¹)
    dsimp [rem]
    rw [← sub_div, ← sub_div]
    exact div_nonneg (by linarith) (sq_nonneg _)
  · let C := Real.log 4 + 4
    have hmajor := (integrableOn_Ioi_rpow_of_lt (a := -(9 / 5 : ℝ)) (by norm_num) hx0).const_mul C
    have hc : Real.sqrt x * (∫ t in Ioi x, C * t ^ (-(9 / 5) : ℝ)) =
        C * (5 / 4) * x ^ (-(3 / 10) : ℝ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx0,
        show -(9 / 5 : ℝ) + 1 = -(4 / 5 : ℝ) by norm_num, Real.sqrt_eq_rpow,
        show -(3 / 10 : ℝ) = 1 / 2 + -(4 / 5) by norm_num, Real.rpow_add hx0]
      ring
    rw [← hc]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply setIntegral_mono_on hi hmajor measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := hx0.trans ht
    have hu := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t
    have hb := Chebyshev.psi_le_const_mul_self (x := t ^ (5 : ℝ)⁻¹) (by positivity)
    dsimp [rem]
    rw [← sub_div, ← sub_div, show -(9 / 5 : ℝ) = (5 : ℝ)⁻¹ - 2 by norm_num,
      Real.rpow_sub ht0, Real.rpow_two, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
