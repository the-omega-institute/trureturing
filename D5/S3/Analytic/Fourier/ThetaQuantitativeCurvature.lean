/- GID: D5/S3/Analytic/Fourier/ThetaQuantitativeCurvature
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaQuantitativeCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative consumer of the complete theta fourth-log curvature reserve. -/
import D5.S3.Analytic.Fourier.ThetaRadialCurvature
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

noncomputable section

namespace RhTransient.ThetaQuantitativeCurvature

open Real Set
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open private fullJet fullJet_deriv twoModeJet fullNormalizedJet fullNormalizedNumerator
  normalizedTail normalizedTail_bound twoModeJet_abs_le twoModeNumerator frontBudget tailBudget
  tailExponentialDenominator tail_exp_le weighted_tail_exp_le scaled_rational_perturbation
  fourthNumerator_perturbation absoluteFourth firstModeReserve firstModeReserve_ge
  twoMode_actual_bound fourthNumerator actual_fullJet_normalized
  actual_fullJet_zero_eq_phi_all actual_fullJet_eq_phi_iterated_all
  actual_fullJet_odd_origin logJet1 logJet2 logJet3 logJet4 hasDerivAt_log_four_jets
  squareVariable_strictConcavity_of_fourthJet_neg from
  D5.S3.Analytic.Fourier.ThetaRadialCurvature

/-- The already paid full-tail estimate retains its explicit reserve.
    This is the accepted negative proof before discarding the reserve. -/
private theorem fullNormalizedNumerator_reserve {y : ℝ} (hy : 3 ≤ y) :
    fullNormalizedNumerator y ≤ -(12623 / 64000 : ℝ) * firstModeReserve y := by
  have hy0 : 0 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  let q := exp (-8*y)
  let C := tailExponentialDenominator
  have hC : 0 < C := by norm_num [C,tailExponentialDenominator]
  have hq : 0 ≤ q := exp_nonneg _
  have hqcap : q ≤ 1/C := tail_exp_le hy
  have hCs0 : 0 ≤ C*q := mul_nonneg hC.le hq
  have hCs1 : C*q ≤ 1 := by
    have hCn : C ≠ 0 := ne_of_gt hC
    calc
      _ ≤ C*(1/C) := mul_le_mul_of_nonneg_left hqcap hC.le
      _ = 1 := by field_simp [hCn]
  have ha (k : ℕ) (hk : k ≤ 4) := twoModeJet_abs_le k hk hy
  have hr (k : ℕ) (hk : k ≤ 4) := (normalizedTail_bound k hk hy).2
  have hp := fourthNumerator_perturbation
    (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega))
    (ha 3 (by omega)) (ha 4 (by omega))
    (hr 0 (by omega)) (hr 1 (by omega)) (hr 2 (by omega))
    (hr 3 (by omega)) (hr 4 (by omega))
  let delta : ℝ :=
    absoluteFourth (frontBudget 0+tailBudget 0*q) (frontBudget 1+tailBudget 1*q)
      (frontBudget 2+tailBudget 2*q) (frontBudget 3+tailBudget 3*q)
      (frontBudget 4+tailBudget 4*q) -
    absoluteFourth (frontBudget 0) (frontBudget 1) (frontBudget 2)
      (frontBudget 3) (frontBudget 4)
  have hp' : |fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y))| ≤
      y^12*delta := by
    calc
      _ ≤ _ := hp
      _ = _ := by
        dsimp [delta,q,absoluteFourth]
        ring
  have hdelta : delta ≤ C*q/2 := by
    have h := scaled_rational_perturbation hCs0 hCs1
    convert h using 1 <;>
      dsimp [delta,C,tailExponentialDenominator] <;> norm_num <;> ring
  have hweighted : y^3*q ≤ 27/C := weighted_tail_exp_le hy
  have herror : y^12*delta ≤ (27/512:ℝ)*firstModeReserve y := by
    calc
      _ ≤ y^12*(C*q/2) := mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = (y^9*C/2)*(y^3*q) := by ring
      _ ≤ (y^9*C/2)*(27/C) :=
        mul_le_mul_of_nonneg_left hweighted (by positivity)
      _ = (27/512:ℝ)*(256*y^9) := by
        dsimp [C,tailExponentialDenominator]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (firstModeReserve_ge hy) (by norm_num)
  have hreserve : 0 < firstModeReserve y :=
    (show 0 < 256*y^9 by positivity).trans_le (firstModeReserve_ge hy)
  have hfront := twoMode_actual_bound hy
  have hdiff := (le_abs_self
    (fullNormalizedNumerator y-twoModeNumerator y (exp (-3*y)))).trans hp'
  have hfull : fullNormalizedNumerator y ≤
      -(12623/64000:ℝ)*firstModeReserve y := by
    linarith
  exact hfull

private theorem fullNormalizedJet_zero_abs_le {y : ℝ} (hy : 3 ≤ y) :
    |fullNormalizedJet 0 y| ≤ (41 / 10 : ℝ) * y ^ 2 := by
  have htail := (normalizedTail_bound 0 (by omega) hy).2
  have he := tail_exp_le hy
  have hb : frontBudget 0 + tailBudget 0 / tailExponentialDenominator ≤ (41 / 10 : ℝ) := by
    norm_num [frontBudget, tailBudget, tailExponentialDenominator]
  calc
    _ ≤ |twoModeJet 0 y (exp (-3 * y))| + |normalizedTail 0 y| := abs_add_le _ _
    _ ≤ frontBudget 0 * y ^ 2 + tailBudget 0 * y ^ 2 * exp (-8 * y) :=
      add_le_add (by simpa using twoModeJet_abs_le 0 (by omega) hy)
        (by simpa using htail)
    _ ≤ frontBudget 0 * y ^ 2 + tailBudget 0 * y ^ 2 *
        (1 / tailExponentialDenominator) := by
      have htb : 0 ≤ tailBudget 0 := by
        norm_num [tailBudget]
      have hfac : 0 ≤ tailBudget 0 * y ^ 2 :=
        mul_nonneg htb (sq_nonneg y)
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left he hfac)
    _ = (frontBudget 0 + tailBudget 0 / tailExponentialDenominator) * y ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg y)

/-- Every normalization factor cancels before the logarithmic quotient is bounded. -/
private theorem fullNormalized_log_fourth_le {y : ℝ} (hy : 3 ≤ y)
    (hf : 0 < fullNormalizedJet 0 y) :
    fullNormalizedNumerator y / (fullNormalizedJet 0 y) ^ 4 ≤ -y / 6 := by
  have hy0 : 0 < y := by linarith
  have hreserve := fullNormalizedNumerator_reserve hy
  have hB := firstModeReserve_ge hy
  have hN : fullNormalizedNumerator y ≤ -(12623 / 250 : ℝ) * y ^ 9 := by
    have h := mul_le_mul_of_nonpos_left hB (show -(12623 / 64000 : ℝ) ≤ 0 by norm_num)
    calc
      _ ≤ -(12623 / 64000 : ℝ) * firstModeReserve y := hreserve
      _ ≤ -(12623 / 64000 : ℝ) * (256 * y ^ 9) := h
      _ = _ := by ring
  have hF : fullNormalizedJet 0 y ≤ (41 / 10 : ℝ) * y ^ 2 :=
    (le_abs_self _).trans (fullNormalizedJet_zero_abs_le hy)
  have hF4 : (fullNormalizedJet 0 y) ^ 4 ≤ (41 / 10 : ℝ) ^ 4 * y ^ 8 := by
    have h := pow_le_pow_left₀ hf.le hF 4
    calc
      _ ≤ ((41 / 10 : ℝ) * y ^ 2) ^ 4 := h
      _ = (41 / 10 : ℝ) ^ 4 * y ^ 8 := by ring
  have hcoef : (41 / 10 : ℝ) ^ 4 ≤ 6 * (12623 / 250 : ℝ) := by norm_num
  have hpoly : ((41 / 10 : ℝ) ^ 4 / 6) * y ^ 9 ≤ (12623 / 250 : ℝ) * y ^ 9 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  apply (div_le_iff₀ (pow_pos hf 4)).mpr
  calc
    _ ≤ -(12623 / 250 : ℝ) * y ^ 9 := hN
    _ ≤ -((41 / 10 : ℝ) ^ 4 / 6) * y ^ 9 := by linarith [hpoly]
    _ = (-y / 6) * ((41 / 10 : ℝ) ^ 4 * y ^ 8) := by ring
    _ ≤ _ := mul_le_mul_of_nonpos_left hF4 (by linarith)

private theorem actual_logJet4_bound {x : ℝ} (hx : 0 ≤ x) :
    logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4) x ≤
      -(Real.pi * exp (2 * x)) / 6 := by
  let y : ℝ := Real.pi * exp (2 * x)
  let E : ℝ := exp (x / 2 - y)
  have hy : 3 ≤ y := by
    have he : 1 ≤ exp (2 * x) := one_le_exp (by linarith)
    dsimp [y]
    nlinarith [Real.pi_gt_three]
  have hE : 0 < E := exp_pos _
  have hp : 0 < fullJet 0 x := by
    rw [actual_fullJet_zero_eq_phi_all, romikPhi_eq_source]
    exact (source_theta_gaussian_bound x).1
  have hn0 : fullJet 0 x = E * fullNormalizedJet 0 y :=
    actual_fullJet_normalized 0 (by omega) hx
  have hF : 0 < fullNormalizedJet 0 y :=
    (mul_pos_iff_of_pos_left hE).mp (hn0 ▸ hp)
  have heq :
      logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4) x =
        fullNormalizedNumerator y / (fullNormalizedJet 0 y) ^ 4 := by
    change fourthNumerator (fullJet 0 x) (fullJet 1 x) (fullJet 2 x)
      (fullJet 3 x) (fullJet 4 x) / (fullJet 0 x) ^ 4 = _
    rw [actual_fullJet_normalized 0 (by omega) hx,
      actual_fullJet_normalized 1 (by omega) hx,
      actual_fullJet_normalized 2 (by omega) hx,
      actual_fullJet_normalized 3 (by omega) hx,
      actual_fullJet_normalized 4 (by omega) hx]
    change fourthNumerator (E * fullNormalizedJet 0 y) (E * fullNormalizedJet 1 y)
      (E * fullNormalizedJet 2 y) (E * fullNormalizedJet 3 y)
      (E * fullNormalizedJet 4 y) / (E * fullNormalizedJet 0 y) ^ 4 = _
    have hnum : fourthNumerator (E * fullNormalizedJet 0 y) (E * fullNormalizedJet 1 y)
        (E * fullNormalizedJet 2 y) (E * fullNormalizedJet 3 y)
        (E * fullNormalizedJet 4 y) = E ^ 4 * fullNormalizedNumerator y := by
      dsimp only [fourthNumerator, fullNormalizedNumerator]
      ring
    rw [hnum, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 4 (ne_of_gt hE))]
  rw [heq]
  exact fullNormalized_log_fourth_le hy hF

private theorem actual_log_fourth_derivative_bound {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv 4 (fun t : ℝ => log (romikPhi t)) x ≤
      -(Real.pi * exp (2 * x)) / 6 := by
  let e0 : ℝ → ℝ := fun t => log (fullJet 0 t)
  let e1 := logJet1 (fullJet 0) (fullJet 1)
  let e2 := logJet2 (fullJet 0) (fullJet 1) (fullJet 2)
  let e3 := logJet3 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3)
  let e4 := logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
  have hd (t : ℝ) := hasDerivAt_log_four_jets
    (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
    (fullJet_deriv 0 t) (fullJet_deriv 1 t) (fullJet_deriv 2 t) (fullJet_deriv 3 t)
    (by
      rw [actual_fullJet_zero_eq_phi_all, romikPhi_eq_source]
      exact (source_theta_gaussian_bound t).1.ne')
  have he01 : deriv e0 = e1 := funext (fun t => (hd t).1.deriv)
  have he12 : deriv e1 = e2 := funext (fun t => (hd t).2.1.deriv)
  have he23 : deriv e2 = e3 := funext (fun t => (hd t).2.2.1.deriv)
  have he34 : deriv e3 = e4 := funext (fun t => (hd t).2.2.2.deriv)
  have hephi : e0 = fun t : ℝ => log (romikPhi t) := by
    funext t
    simp only [e0, actual_fullJet_zero_eq_phi_all]
  have hid : iteratedDeriv 4 e0 = e4 := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ,
      show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ,
      iteratedDeriv_one, he01, he12, he23, he34]
  rw [← hephi, hid]
  exact actual_logJet4_bound hx

private theorem actual_log_fourth_derivative_uniform_bound {x : ℝ} (hx : 0 ≤ x) :
    iteratedDeriv 4 (fun t : ℝ => log (romikPhi t)) x ≤
        -(Real.pi * exp (2 * x)) / 6 ∧
      -(Real.pi * exp (2 * x)) / 6 < -(1 / 2 : ℝ) := by
  refine ⟨actual_log_fourth_derivative_bound hx, ?_⟩
  have he : 1 ≤ exp (2 * x) := one_le_exp (by linarith)
  nlinarith [Real.pi_gt_three]

/-- A fixed quadratic correction in the square variable is strictly concave.
    Its fourth logarithmic source jet is ell''''+1/2<0. -/
theorem actual_square_strong_concavity :
    StrictConcaveOn ℝ (Ioi (0 : ℝ))
      (fun r : ℝ => log (romikPhi (sqrt r)) + r ^ 2 / 48) := by
  let e0 : ℝ → ℝ := fun t => log (fullJet 0 t)
  let e1 := logJet1 (fullJet 0) (fullJet 1)
  let e2 := logJet2 (fullJet 0) (fullJet 1) (fullJet 2)
  let e3 := logJet3 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3)
  let e4 := logJet4 (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
  have hd (t : ℝ) := hasDerivAt_log_four_jets
    (fullJet 0) (fullJet 1) (fullJet 2) (fullJet 3) (fullJet 4)
    (fullJet_deriv 0 t) (fullJet_deriv 1 t) (fullJet_deriv 2 t) (fullJet_deriv 3 t)
    (by
      rw [actual_fullJet_zero_eq_phi_all, romikPhi_eq_source]
      exact (source_theta_gaussian_bound t).1.ne')
  let g0 : ℝ → ℝ := fun t => e0 t + t ^ 4 / 48
  let g1 : ℝ → ℝ := fun t => e1 t + t ^ 3 / 12
  let g2 : ℝ → ℝ := fun t => e2 t + t ^ 2 / 4
  let g3 : ℝ → ℝ := fun t => e3 t + t / 2
  let g4 : ℝ → ℝ := fun t => e4 t + 1 / 2
  have h01 (t : ℝ) : HasDerivAt g0 (g1 t) t := by
    convert! ((hd t).1.add (((hasDerivAt_id t).pow 4).div_const 48)) using 1 <;>
      simp only [g0, g1, Pi.pow_apply, id_eq, show (4 : ℕ) - 1 = 3 by rfl] <;> ring
  have h12 (t : ℝ) : HasDerivAt g1 (g2 t) t := by
    convert! ((hd t).2.1.add (((hasDerivAt_id t).pow 3).div_const 12)) using 1 <;>
      simp only [g1, g2, Pi.pow_apply, id_eq, show (3 : ℕ) - 1 = 2 by rfl] <;> ring
  have h23 (t : ℝ) : HasDerivAt g2 (g3 t) t := by
    convert! ((hd t).2.2.1.add (((hasDerivAt_id t).pow 2).div_const 4)) using 1 <;>
      simp only [g2, g3, Pi.pow_apply, id_eq, show (2 : ℕ) - 1 = 1 by rfl, pow_one] <;> ring
  have h34 (t : ℝ) : HasDerivAt g3 (g4 t) t := by
    simpa only [g3, g4, id_eq] using! (hd t).2.2.2.add ((hasDerivAt_id t).div_const 2)
  have h10 : g1 0 = 0 := by
    simp only [g1, e1, logJet1, actual_fullJet_odd_origin.1, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
      zero_div, add_zero]
  have h30 : g3 0 = 0 := by
    simp [g3, e3, logJet3, actual_fullJet_odd_origin.1, actual_fullJet_odd_origin.2]
  have h4neg (t : ℝ) (ht : 0 < t) : g4 t < 0 := by
    have hb := actual_logJet4_bound ht.le
    have hy : 3 < Real.pi * exp (2 * t) := by
      have he : 1 ≤ exp (2 * t) := one_le_exp (by positivity)
      nlinarith [Real.pi_gt_three]
    change e4 t + 1 / 2 < 0
    linarith
  have h := squareVariable_strictConcavity_of_fourthJet_neg g0 g1 g2 g3 g4
    (fun t _ => h01 t) (fun t _ => h12 t) (fun t _ => h23 t) (fun t _ => h34 t)
    h10 h30 h4neg
  apply h.2.congr
  intro r hr
  have hr0 : 0 < r := hr
  dsimp only [g0, e0]
  rw [actual_fullJet_zero_eq_phi_all]
  have hsq := sq_sqrt hr0.le
  have hfour : (sqrt r) ^ 4 = r ^ 2 := by
    calc
      _ = ((sqrt r) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [hfour]

end RhTransient.ThetaQuantitativeCurvature
