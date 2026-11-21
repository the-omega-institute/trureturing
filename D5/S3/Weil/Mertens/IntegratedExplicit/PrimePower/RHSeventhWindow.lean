/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHSeventhWindow
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHSeventhWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed sixth and seventh terms and the actual cube spectrum on an RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RootSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SeventhCutoff

/-! The signed sixth and seventh terms and the actual cube spectrum on an RH prime window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Real Set
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualH)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
  (G abs_G_sub_normalized_actualH_le)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

/-- At root degree two the general density equals the square-cutoff density. -/
private theorem rootDensity_two (u : ℝ) : rootDensity 2 u = squareDensity u := by
  have h := root_spectral_transform (r := 2) (by norm_num) (u / 2)
  dsimp only at h
  rw [show (2 : ℝ) * (u / 2) = u by ring] at h
  rw [← h, ← square_spectral_transform u]
  simp only [show (1 : ℝ) - 2 / 2 = 0 by norm_num, zero_mul, Real.exp_zero, mul_one,
    show (2 : ℝ) - 1 = 1 by norm_num, one_mul]


private theorem cubePrimitive_eq (x : ℝ) : rootPrimitive 3 x =
    18 * (∑' k, (x : ℂ) ^ (actualZero k / 3 - 1 / 2) /
        (actualZero k * (3 - actualZero k) * (3 - 2 * actualZero k))).re := by
  change (∑' k : ℕ, (2 * (3 : ℂ)^2) * (x : ℂ) ^ (actualZero k / 3 - 1 / 2) /
    (actualZero k * (3 - actualZero k) * (3 - 2 * actualZero k))).re = _
  norm_num
  simp_rw [mul_div_assoc, tsum_mul_left]
  norm_num [Complex.mul_re]

private theorem sixth_seventh_density_bound (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 5000 ^ (7 : ℝ) ≤ x →
      |Real.sqrt x * (Q x - primeTail x) - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) -
        squareDensity (Real.log x) - (5 / 4) * x ^ (-(3 / 10) : ℝ) +
        (6 / 5) * x ^ (-(1 / 3) : ℝ) - rootDensity 3 (Real.log x) -
        (7 / 6) * x ^ (-(5 / 14) : ℝ)| ≤ K * x ^ (-(3 / 8) : ℝ) := by
  obtain ⟨D, hD, hR⟩ := sixth_seventh_normalized hRH
  have hC : 0 ≤ C := abs_nonneg _
  have hM : 0 ≤ M := add_nonneg (mass_nonneg hRH) hC
  refine ⟨D + 3 * C + 5 * C + 10 * M, by positivity, ?_⟩
  intro x hx
  have hx5000 : 5000 ≤ x := le_trans
    (self_le_rpow_of_one_le (by norm_num) (by norm_num : (1 : ℝ) ≤ 7)) hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hm₂ := root_tail_main (r := 2) (by norm_num) hx0
  change _ = _ + centered 2 x at hm₂
  rw [show (2 : ℝ) / (2 - 1) = 2 by norm_num,
      show (2 : ℝ)⁻¹ - 1 / 2 = 0 by norm_num, Real.rpow_zero, mul_one] at hm₂
  have hm₃ := root_tail_main (r := 3) (by norm_num) hx0
  change _ = _ + centered 3 x at hm₃
  rw [show (3 : ℝ) / (3 - 1) = 3 / 2 by norm_num,
      show (3 : ℝ)⁻¹ - 1 / 2 = -(1 / 6) by norm_num] at hm₃
  have hm₅ := root_tail_main (r := 5) (by norm_num) hx0
  change _ = _ + centered 5 x at hm₅
  rw [show (5 : ℝ) / (5 - 1) = 5 / 4 by norm_num,
      show (5 : ℝ)⁻¹ - 1 / 2 = -(3 / 10) by norm_num] at hm₅
  let err := Real.sqrt x * (Q x - primeTail x -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
        (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2)) +
        (6 / 5) * x ^ (-(1 / 3) : ℝ) - (7 / 6) * x ^ (-(5 / 14) : ℝ)
  have hsplit : Real.sqrt x * (Q x - primeTail x) - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) -
      squareDensity (Real.log x) - (5 / 4) * x ^ (-(3 / 10) : ℝ) +
      (6 / 5) * x ^ (-(1 / 3) : ℝ) - rootDensity 3 (Real.log x) -
      (7 / 6) * x ^ (-(5 / 14) : ℝ) =
      err + (centered 2 x - squareDensity (Real.log x)) +
        (centered 3 x - rootDensity 3 (Real.log x)) + centered 5 x := by
    dsimp only [err]
    linear_combination hm₂ + hm₃ + hm₅
  have hv : Real.log 2 ≤ Real.log x / 3 := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 8) (by linarith : 8 ≤ x)
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at hl
    norm_num at hl
    linarith
  have hc := root_centered_error (r := 3) (by norm_num) hv
  rw [show (3 : ℝ) * (Real.log x / 3) = Real.log x by ring, Real.exp_log hx0] at hc
  have exp_to_pow : Real.exp (-Real.log x / 2) = x ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [exp_to_pow, show (2 * 3 - 1 : ℝ) = 5 by norm_num] at hc
  have hv₂ : Real.log 2 ≤ Real.log x / 2 := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : 4 ≤ x)
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hl
    norm_num at hl
    linarith
  have hs := root_centered_error (r := 2) (by norm_num) hv₂
  rw [show (2 : ℝ) * (Real.log x / 2) = Real.log x by ring, Real.exp_log hx0,
    rootDensity_two, exp_to_pow, show (2 * 2 - 1 : ℝ) = 3 by norm_num] at hs
  have h₂p := Real.rpow_le_rpow_of_exponent_le hx1
    (show -(1 / 2 : ℝ) ≤ -(3 / 8) by norm_num)
  have h₅p := Real.rpow_le_rpow_of_exponent_le hx1
    (show -(2 / 5 : ℝ) ≤ -(3 / 8) by norm_num)
  rw [hsplit]
  calc
    _ ≤ |err| + |centered 2 x - squareDensity (Real.log x)| +
        |centered 3 x - rootDensity 3 (Real.log x)| + |centered 5 x| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ D * x ^ (-(3 / 8) : ℝ) + (3 * C) * x ^ (-(3 / 8) : ℝ) +
        (5 * C) * x ^ (-(3 / 8) : ℝ) + (10 * M) * x ^ (-(3 / 8) : ℝ) :=
      add_le_add (add_le_add (add_le_add (hR x hx)
        (hs.trans (mul_le_mul_of_nonneg_left h₂p (by positivity))))
        (hc.trans (mul_le_mul_of_nonneg_left h₂p (by positivity))))
        ((fifth_centered_error hRH (by linarith)).trans (mul_le_mul_of_nonneg_left h₅p (by positivity)))
    _ = _ := by ring

open Filter
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

theorem prime_window_seventh_of_rh (hRH : RiemannHypothesis) :
    let A₃ (x : ℝ) := 18 * (∑' k, (x : ℂ) ^ (actualZero k / 3 - 1 / 2) /
      (actualZero k * (3 - actualZero k) * (3 - 2 * actualZero k))).re
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |(∫ x in a..B, max (-primeTail x) 0 / Real.sqrt x) - 2 * Real.log (B / a) -
        spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
        9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
        (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) +
        (18 / 5) * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ)) -
        A₃ B + A₃ a -
        (49 / 15) * (a ^ (-(5 / 14) : ℝ) - B ^ (-(5 / 14) : ℝ))| ≤
          K * (a ^ (-(3 / 8) : ℝ) - B ^ (-(3 / 8) : ℝ)) := by
  dsimp only
  simp_rw [← cubePrimitive_eq]
  obtain ⟨T, hT⟩ := eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨D, hD, hD_bound⟩ := sixth_seventh_density_bound hRH
  have hC : 0 ≤ C := abs_nonneg _
  let X : ℝ := 5000 ^ (7 : ℝ)
  let K := D + C
  have hX5000 : 5000 ≤ X :=
    self_le_rpow_of_one_le (by norm_num) (by norm_num)
  have hX2 : 2 ≤ X := by linarith
  refine ⟨max T X, K / (3 / 8), hX2.trans (le_max_right _ _),
    by dsimp [K]; positivity, ?_⟩
  intro a B ha hab
  have haX := (le_max_right T X).trans ha
  have ha2 := hX2.trans haX
  have ha0 : 0 < a := by linarith
  have hB0 := ha0.trans_le hab
  have hlog := Real.log_le_log ha0 hab
  have hEq : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1
    have hpos := hT _ ((le_max_left T X).trans (ha.trans hx))
    have hscaled := complete_scaled (x := Real.exp u) (ha2.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  let e (u : ℝ) := rootWindowDensity u - (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) -
    squareDensity u - (5 / 4) * Real.exp (-(3 / 10 : ℝ) * u) +
    (6 / 5) * Real.exp (-(1 / 3 : ℝ) * u) - rootDensity 3 u -
    (7 / 6) * Real.exp (-(5 / 14 : ℝ) * u)
  have hE (u : ℝ) (hu : u ∈ Set.Icc (Real.log a) (Real.log B)) :
      |e u| ≤ K * Real.exp (-(3 / 8 : ℝ) * u) := by
    have hx : X ≤ Real.exp u :=
      haX.trans (by simpa [Real.exp_log ha0] using Real.exp_le_exp.mpr hu.1)
    have hu0 : 0 ≤ u := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_zero]
      linarith
    have h := hD_bound (Real.exp u) hx
    have hexp (p : ℝ) : (Real.exp u) ^ p = Real.exp (p * u) := by
      rw [← Real.exp_mul, mul_comm]
    simp only [Real.log_exp, hexp] at h
    have hG := (abs_G_sub_normalized_actualH_le hu0).le
    have hg : |G u - Real.exp (-u / 2) * (actualH u).re| ≤
        C * Real.exp (-(3 / 8 : ℝ) * u) := by
      refine hG.trans ?_
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) hC
    have hsplit : ∀ b c d f g h i : ℝ,
        b - 2 + c - d - f - g + h - i = (b - 2 - d - f - g + h - i) + c := by
      intros
      ring
    have hh : e u =
        (Real.sqrt (Real.exp u) * (Q (Real.exp u) - primeTail (Real.exp u)) - 2 -
          (3 / 2) * Real.exp (-(1 / 6 : ℝ) * u) - squareDensity u -
          (5 / 4) * Real.exp (-(3 / 10 : ℝ) * u) + (6 / 5) * Real.exp (-(1 / 3 : ℝ) * u) -
          rootDensity 3 u - (7 / 6) * Real.exp (-(5 / 14 : ℝ) * u)) +
        (G u - Real.exp (-u / 2) * (actualH u).re) := by unfold e rootWindowDensity; ring
    rw [hh]
    exact (abs_add_le _ _).trans ((add_le_add h hg).trans_eq (by dsimp [K]; ring))
  have hi (c r : ℝ) :
      IntervalIntegrable (fun u : ℝ => c * Real.exp (-r * u)) volume (Real.log a) (Real.log B) :=
    (by fun_prop : Continuous (fun u : ℝ => c * Real.exp (-r * u))).intervalIntegrable _ _
  have hd : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      intro u hu
      exact (Real.log_le_log (by norm_num) ha2).trans hu.1)).intervalIntegrable
  obtain ⟨hsq, hsquare⟩ := square_density_integral (Real.log a) (Real.log B)
  obtain ⟨hcu, hcube⟩ := root_density_integral (r := 3) (by norm_num) (Real.log a) (Real.log B)
  have h₂ := hd.sub (hi (3 / 2) (1 / 6))
  have h₃ := h₂.sub hsq
  have h₄ := h₃.sub (hi (5 / 4) (3 / 10))
  have h₅ := h₄.add (hi (6 / 5) (1 / 3))
  have h₆ := h₅.sub hcu
  have hI : IntervalIntegrable e volume (Real.log a) (Real.log B) := h₆.sub (hi (7 / 6) (5 / 14))
  have h := (intervalIntegral.abs_integral_le_integral_abs hlog (f := e)).trans
    (intervalIntegral.integral_mono_on hlog hI.abs (hi K (3 / 8)) hE)
  dsimp only [e] at h
  have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [intervalIntegral.integral_sub h₆ (hi (7 / 6) (5 / 14)),
    intervalIntegral.integral_sub h₅ hcu, intervalIntegral.integral_add h₄ (hi (6 / 5) (1 / 3)),
    intervalIntegral.integral_sub h₃ (hi (5 / 4) (3 / 10)), intervalIntegral.integral_sub h₂ hsq,
    intervalIntegral.integral_sub hd (hi (3 / 2) (1 / 6)), hsquare, hcube,
    Real.exp_log hB0, Real.exp_log ha0] at h
  simp only [intervalIntegral.integral_const_mul,
    exp_decay_integral (by norm_num : (0 : ℝ) < 1 / 6),
    exp_decay_integral (by norm_num : (0 : ℝ) < 3 / 10),
    exp_decay_integral (by norm_num : (0 : ℝ) < 1 / 3),
    exp_decay_integral (by norm_num : (0 : ℝ) < 5 / 14),
    exp_decay_integral (by norm_num : (0 : ℝ) < 3 / 8),
    hrpow ha0, hrpow hB0] at h
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
      (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) +
      (18 / 5) * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ)) -
      rootPrimitive 3 B + rootPrimitive 3 a -
      (49 / 15) * (a ^ (-(5 / 14) : ℝ) - B ^ (-(5 / 14) : ℝ))| ≤ _
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha2 hab, hEq]
  convert h using 1
  · congr 1
    ring
  · ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
