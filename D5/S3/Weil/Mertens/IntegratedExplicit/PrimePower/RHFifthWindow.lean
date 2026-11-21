/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fifth-root coefficient and a common-endpoint remainder for RH prime windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

/-! The fifth-root main term contributes on the same log window as both spectral
primitives. The sixth-root arithmetic envelope is integrated with the actual endpoints. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G abs_G_sub_normalized_actualH_le)


open D5.S3.Weil.Mertens.IntegratedExplicit (actualH)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff (exists_abs_psi_sub_roots_le)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (tail_eq diff_integrable)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

private theorem centered_root_tail_bound {r x M : ℝ} (hr : 1 < r) (hx : 1 ≤ x) (hM : 0 ≤ M)
    (hQ : |Q (x ^ r⁻¹)| ≤ M * (x ^ r⁻¹) ^ (-(1 / 2) : ℝ))
    (hI : |∫ s in Ioi (x ^ r⁻¹), s ^ (-r) * Q s| ≤
      M / (r - 1 / 2) * (x ^ r⁻¹) ^ (1 / 2 - r)) :
    |Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2)| ≤
      (2 * r * M) * x ^ ((2 * r)⁻¹ - 1 / 2) := by
  let y := x ^ r⁻¹
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hpow (d : ℝ) : 0 ≤ y ^ d := Real.rpow_nonneg hy0.le _
  have hQ' : |Q y| ≤ M * y ^ (-(1 / 2) : ℝ) := hQ
  have hI' : |∫ s in Ioi y, s ^ (-r) * Q s| ≤
      M / (r - 1 / 2) * y ^ (1 / 2 - r) := hI
  have hI'' : (r - 1) * |∫ s in Ioi y, s ^ (-r) * Q s| ≤
      M * y ^ (1 / 2 - r) := by
    have hfactor : (r - 1) * (M / (r - 1 / 2)) ≤ M := by
      rw [← mul_div_assoc, div_le_iff₀ (show 0 < r - 1 / 2 by linarith)]
      nlinarith
    calc
      _ ≤ (r - 1) * (M / (r - 1 / 2) * y ^ (1 / 2 - r)) :=
        mul_le_mul_of_nonneg_left hI' (sub_nonneg.mpr hr.le)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hfactor (hpow _)
  have hscale : Real.sqrt x * y ^ (1 / 2 - r) = x ^ ((2 * r)⁻¹ - 1 / 2) := by
    dsimp [y]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    field_simp
    ring
  have ht := centered_root_tail (r := r) hr.le (zero_lt_one.trans_le hx)
  change _ = r * Real.sqrt x *
    (Q y * y ^ (1 - r) - (r - 1) * (∫ s in Ioi y, s ^ (-r) * Q s)) at ht
  rw [ht, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r * Real.sqrt x)]
  calc
    _ ≤ r * Real.sqrt x * (|Q y| * y ^ (1 - r) +
      (r - 1) * |∫ s in Ioi y, s ^ (-r) * Q s|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_mul,
        abs_of_nonneg (hpow _), abs_of_nonneg (sub_nonneg.mpr hr.le)])
    _ ≤ r * Real.sqrt x * (M * y ^ (1 / 2 - r) + M * y ^ (1 / 2 - r)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ hI'') (by positivity)
      exact (mul_le_mul_of_nonneg_right hQ' (hpow _)).trans_eq (by
        rw [mul_assoc, ← Real.rpow_add hy0, show -(1 / 2 : ℝ) + (1 - r) = 1 / 2 - r by ring])
    _ = _ := by rw [← hscale]; ring

private theorem normalized_tail_bound {g : ℝ → ℝ} {x C p : ℝ}
    (hx : 0 < x) (hp : p < 1)
    (hf : AEStronglyMeasurable (fun t => g t / t ^ 2) (volume.restrict (Ioi x)))
    (hg : ∀ t > x, |g t| ≤ C * t ^ p) :
    |Real.sqrt x * (∫ t in Ioi x, g t / t ^ 2)| ≤ C / (1 - p) * x ^ (p - 1 / 2) := by
  have hmajor : IntegrableOn (fun t => C * t ^ (p - 2)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul C
  have hpoint (t : ℝ) (ht : t ∈ Ioi x) : ‖g t / t ^ 2‖ ≤ C * t ^ (p - 2) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg t),
      Real.rpow_sub (hx.trans ht), Real.rpow_two, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hg t ht) (sq_nonneg _)
  have hI : IntegrableOn (fun t => g t / t ^ 2) (Ioi x) :=
    hmajor.mono' hf (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpoint t ht)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt x * (∫ t in Ioi x, C * t ^ (p - 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      rw [← Real.norm_eq_abs]
      exact (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_on hI.norm hmajor measurableSet_Ioi hpoint)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx, Real.sqrt_eq_rpow,
        show p - 1 / 2 = 1 / 2 + (p - 2 + 1) by ring, Real.rpow_add hx (1 / 2) (p - 2 + 1),
        show p - 2 + 1 = -(1 - p) by ring]
      simp only [div_neg]
      ring


private theorem fifth_cutoff_integrated_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 2 ≤ x →
      |Real.sqrt x * (Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2))| ≤
        D * x ^ (-(1 / 3) : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_psi_sub_roots_le
  refine ⟨C / (1 - 1 / 6), by positivity, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h₂ := root_kernel_integrable (p := (2 : ℝ)⁻¹) (by norm_num) hx0
  have h₃ := root_kernel_integrable (p := (3 : ℝ)⁻¹) (by norm_num) hx0
  have h₅ := root_kernel_integrable (p := (5 : ℝ)⁻¹) (by norm_num) hx0
  have hd := diff_integrable.mono_set (Ioi_subset_Ioi hx1)
  let f (t : ℝ) := Chebyshev.psi t - Chebyshev.theta t -
    Chebyshev.psi (t ^ (2 : ℝ)⁻¹) -
    Chebyshev.psi (t ^ (3 : ℝ)⁻¹) -
    Chebyshev.psi (t ^ (5 : ℝ)⁻¹)
  have hfn (t : ℝ) : f t / t ^ 2 = (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 -
      Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2 -
      Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2 -
      Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2 := by
    simp only [f, sub_div]
  have hf : IntegrableOn (fun t => f t / t ^ 2) (Ioi x) := by
    simp_rw [hfn]
    exact ((hd.sub h₂).sub h₃).sub h₅
  have hform :
      (∫ t in Ioi x, f t / t ^ 2) = Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2) := by
    rw [tail_eq hx1]
    refine (setIntegral_congr_fun measurableSet_Ioi (fun t _ => hfn t)).trans ?_
    exact (integral_sub ((hd.sub h₂).sub h₃) h₅).trans
      (congrArg (· - (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2))
        ((integral_sub (hd.sub h₂) h₃).trans
          (congrArg (· - (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2))
            (integral_sub hd h₂))))
  rw [← hform]
  have h := normalized_tail_bound (p := 1 / 6) hx0 (by norm_num)
    hf.aestronglyMeasurable (fun t ht => by
      simpa [f, one_div] using hbound t (hx.trans ht.le))
  convert h using 1
  norm_num

private theorem normalized_fifth_density_bound (x D C₂ C₃ C₅ : ℝ)
    (hx : 2 ≤ x) (h₂₀ : 0 ≤ C₂) (h₅₀ : 0 ≤ C₅)
    (hR : |Real.sqrt x * (Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2))| ≤
        D * x ^ (-(1 / 3) : ℝ))
    (h₂ : |Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ (2 : ℝ)⁻¹) - t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        squareDensity (Real.log x)| ≤ C₂ * x ^ (-(1 / 2) : ℝ))
    (h₃ : |Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ (3 : ℝ)⁻¹) - t ^ (3 : ℝ)⁻¹) / t ^ 2)| ≤
        C₃ * x ^ (-(1 / 3) : ℝ))
    (h₅ : |Real.sqrt x * (∫ t in Ioi x, (Chebyshev.psi (t ^ (5 : ℝ)⁻¹) - t ^ (5 : ℝ)⁻¹) / t ^ 2)| ≤
        C₅ * x ^ (-(2 / 5) : ℝ)) :
    |Real.sqrt x * (Q x - primeTail x) - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) -
      squareDensity (Real.log x) - (5 / 4) * x ^ (-(3 / 10) : ℝ)| ≤
      (D + C₂ + C₃ + C₅) * x ^ (-(1 / 3) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hm₂ := root_tail_main (r := 2) (by norm_num) hx0
  rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num,
      show (2 : ℝ)⁻¹ - 1 / 2 = 0 by norm_num, Real.rpow_zero, mul_one] at hm₂
  have hm₃ := root_tail_main (r := 3) (by norm_num) hx0
  rw [show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num,
      show (3 : ℝ)⁻¹ - 1 / 2 = -(1 / 6) by norm_num] at hm₃
  have hm₅ := root_tail_main (r := 5) (by norm_num) hx0
  rw [show (5 : ℝ) / (5 - 1) = 5 / 4 by norm_num,
      show (5 : ℝ)⁻¹ - 1 / 2 = -(3 / 10) by norm_num] at hm₅
  let err := Real.sqrt x * (Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2))
  let center (r : ℝ) := Real.sqrt x *
    (∫ t in Ioi x, (Chebyshev.psi (t ^ r⁻¹) - t ^ r⁻¹) / t ^ 2)
  have hsplit : Real.sqrt x * (Q x - primeTail x) - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) -
      squareDensity (Real.log x) - (5 / 4) * x ^ (-(3 / 10) : ℝ) =
      err + (center 2 - squareDensity (Real.log x)) + center 3 + center 5 := by
    dsimp only [err, center]
    linear_combination hm₂ + hm₃ + hm₅
  have h₂p := Real.rpow_le_rpow_of_exponent_le hx1
    (show -(1 / 2 : ℝ) ≤ -(1 / 3) by norm_num)
  have h₅p := Real.rpow_le_rpow_of_exponent_le hx1
    (show -(2 / 5 : ℝ) ≤ -(1 / 3) by norm_num)
  rw [hsplit]
  calc
    _ ≤ |err| + |center 2 - squareDensity (Real.log x)| + |center 3| + |center 5| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ D * x ^ (-(1 / 3) : ℝ) + C₂ * x ^ (-(1 / 3) : ℝ) +
        C₃ * x ^ (-(1 / 3) : ℝ) + C₅ * x ^ (-(1 / 3) : ℝ) :=
      add_le_add (add_le_add (add_le_add hR
        (h₂.trans (mul_le_mul_of_nonneg_left h₂p h₂₀))) h₃)
        (h₅.trans (mul_le_mul_of_nonneg_left h₅p h₅₀))
    _ = _ := by ring

private theorem transfer_fifth_log_window (hRH : RiemannHypothesis) {a B K : ℝ}
    (ha : 2 ≤ a) (hab : a ≤ B)
    (hpos : ∀ x ≥ a, 0 < Real.sqrt x * (-primeTail x))
    (hE : ∀ u ∈ Icc (Real.log a) (Real.log B),
      |rootWindowDensity u - (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) - squareDensity u -
        (5 / 4) * Real.exp (-(3 / 10 : ℝ) * u)| ≤ K * Real.exp (-(1 / 3 : ℝ) * u)) :
    |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
      (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ))| ≤
      (3 * K) * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ)) := by
  have ha0 : 0 < a := by linarith
  have hB0 := ha0.trans_le hab
  have hlog := Real.log_le_log ha0 hab
  have hEq : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1
    have hscaled := complete_scaled (x := Real.exp u) (ha.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left (hpos _ hx).le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha hab, hEq]
  have hi (c r : ℝ) :
      IntervalIntegrable (fun u : ℝ => c * Real.exp (-r * u)) volume (Real.log a) (Real.log B) :=
    (by fun_prop : Continuous (fun u : ℝ => c * Real.exp (-r * u))).intervalIntegrable _ _
  have hd : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      intro u hu
      exact (Real.log_le_log (by norm_num) ha).trans hu.1)).intervalIntegrable
  obtain ⟨hsq, hsquare⟩ := square_density_integral (Real.log a) (Real.log B)
  let E (u : ℝ) := rootWindowDensity u - (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) -
    squareDensity u - (5 / 4) * Real.exp (-(3 / 10 : ℝ) * u)
  have hI : IntervalIntegrable E volume (Real.log a) (Real.log B) :=
    ((hd.sub (hi (3 / 2) (1 / 6))).sub hsq).sub (hi (5 / 4) (3 / 10))
  have h := (intervalIntegral.abs_integral_le_integral_abs hlog (f := E)).trans
    (intervalIntegral.integral_mono_on hlog hI.abs (hi K (1 / 3)) hE)
  dsimp only [E] at h
  have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [intervalIntegral.integral_sub ((hd.sub (hi (3 / 2) (1 / 6))).sub hsq) (hi (5 / 4) (3 / 10)),
    intervalIntegral.integral_sub (hd.sub (hi (3 / 2) (1 / 6))) hsq,
    intervalIntegral.integral_sub hd (hi (3 / 2) (1 / 6)),
    hsquare, Real.exp_log hB0, Real.exp_log ha0,
    intervalIntegral.integral_const_mul, exp_decay_integral (by norm_num : (0 : ℝ) < 1 / 6),
    intervalIntegral.integral_const_mul, exp_decay_integral (by norm_num : (0 : ℝ) < 3 / 10),
    intervalIntegral.integral_const_mul, exp_decay_integral (by norm_num : (0 : ℝ) < 1 / 3)] at h
  simp only [hrpow ha0, hrpow hB0] at h
  convert h using 1
  · congr 1
    ring
  · ring


private theorem fifth_centered_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 32 ≤ x) :
    |centered 5 x| ≤ (10 * M) * x ^ (-(2 / 5) : ℝ) := by
  let y := x ^ (5 : ℝ)⁻¹
  have hy : 2 ≤ y := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 32) hx
      (by norm_num : (0 : ℝ) ≤ (5 : ℝ)⁻¹)
    rw [show (32 : ℝ) = 2 ^ (5 : ℝ) by norm_num [Real.rpow_natCast],
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num at h
    simpa [y, one_div] using h
  have h₀ : 0 ≤ M := add_nonneg (mass_nonneg hRH) (show 0 ≤ C from abs_nonneg _)
  have hi := (weighted_bound (b := 5) (d := 1 / 2) hy (by norm_num)
    q_continuous (fun _ ht => q_bound hRH ht)).2
  have hI : |∫ s in Ioi y, s ^ (-5 : ℝ) * Q s| ≤ M / (5 - 1 / 2) * y ^ (1 / 2 - 5 : ℝ) := by
    simpa only [show (5 + 1 / 2 - 1 : ℝ) = 5 - 1 / 2 by ring,
      show (1 - (5 + 1 / 2) : ℝ) = 1 / 2 - 5 by ring] using hi
  have h := centered_root_tail_bound (r := 5) (x := x) (by norm_num) (by linarith)
    h₀ (q_bound hRH hy) hI
  change |centered 5 x| ≤ _ at h
  norm_num at h ⊢
  exact h

/-- Under RH the signed prime-only window error after the ordinary spectral primitive,
cube term and square-cutoff primitive has a fifth-root contribution with coefficient
`25 / 6`. The remaining error retains both endpoints at power `-1 / 3`. -/
theorem prime_window_fifth_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |(∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / a) -
        spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
        9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
        (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ))| ≤
          K * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ)) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨D, hD, hR⟩ := fifth_cutoff_integrated_bound
  have hC : 0 ≤ C := abs_nonneg _
  have hM : 0 ≤ M := add_nonneg (mass_nonneg hRH) hC
  let K := D + 4 * C + 9 * M + 10 * M + C
  refine ⟨max T 32, 3 * K, (by norm_num : (2 : ℝ) ≤ 32).trans (le_max_right _ _),
    by dsimp [K]; positivity, ?_⟩
  intro a B ha hab
  have ha32 := (le_max_right T 32).trans ha
  have ha2 : 2 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
      (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ))| ≤ _
  apply transfer_fifth_log_window hRH ha2 hab
    (fun x hx => hT x ((le_max_left _ _).trans (ha.trans hx)))
  intro u hu
  have hx : 32 ≤ Real.exp u :=
    ha32.trans (by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1)
  have hx2 : 2 ≤ Real.exp u := by linarith
  have hu0 : 0 ≤ u := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_zero]
    linarith
  have h := normalized_fifth_density_bound (Real.exp u) D (4 * C) (9 * M) (10 * M)
    hx2 (by positivity) (by positivity) (hR _ hx2)
    (square_error hRH (by linarith)) (cube_error hRH (by linarith)) (fifth_centered_error hRH hx)
  have hexp (r : ℝ) : (Real.exp u) ^ r = Real.exp (r * u) := by
    rw [← Real.exp_mul, mul_comm]
  rw [Real.log_exp, hexp, hexp, hexp] at h
  have hG := (abs_G_sub_normalized_actualH_le hu0).le
  have hg : |G u - Real.exp (-u / 2) * (actualH u).re| ≤
      C * Real.exp (-(1 / 3 : ℝ) * u) := by
    refine hG.trans ?_
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr (by linarith))
      (Real.exp_nonneg _) hC
  have hsplit : ∀ b c d e f : ℝ,
      b - 2 + c - d - e - f = (b - 2 - d - e - f) + c := by
    intros
    ring
  rw [rootWindowDensity, hsplit]
  exact (abs_add_le _ _).trans ((add_le_add h hg).trans_eq (by dsimp [K]; ring))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
