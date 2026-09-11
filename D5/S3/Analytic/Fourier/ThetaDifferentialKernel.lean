/- GID: D5/S3/Analytic/Fourier/ThetaDifferentialKernel
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/ThetaDifferentialKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Differentiate the original theta series with locally summable majorants. -/

import D5.S3.Zeros.Jensen.SourceThetaMomentBounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section
namespace D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open Real Set Filter Topology
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering

/-- Jacobi's theta function on the positive real axis. -/
def theta (t : ℝ) : ℝ := HurwitzZeta.evenKernel 0 t

/-- The polynomially weighted positive-index theta series. -/
def thetaSeries (k : ℕ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ k * exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)

/-- Romik's original differential weight. -/
def omega (t : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * t ^ 2 -
    3 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t) *
    exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * t)

/-- The original kernel, with no absolute value in its argument. -/
def romikPhi (x : ℝ) : ℝ := 2 * exp (x / 2) * omega (exp (2 * x))

/-- The rescaled theta tail whose differential operator gives the kernel. -/
def psi (x : ℝ) : ℝ := exp (x / 2) * (theta (exp (2 * x)) - 1) / 2

/-- The imported Gaussian-series convergence holds at every positive parameter. -/
theorem thetaSeries_summable (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)) :=
  HurwitzKernelBounds.summable_f_nat k 1 ht

/-- A summable majorant, uniform on the ray above any positive lower endpoint. -/
theorem thetaSeries_local_majorant (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * a))) ∧
    ∀ n : ℕ, ∀ t : ℝ, a ≤ t →
      ‖-Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))‖ ≤
      Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * a)) := by
  refine ⟨(thetaSeries_summable (k + 2) ha).mul_left Real.pi, ?_⟩
  intro n t ht
  rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos pi_pos,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left ht
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr pi_pos.le) (sq_nonneg _))

private theorem term_hasDerivAt (k n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ((n : ℝ) + 1) ^ k *
      exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      (-Real.pi * (((n : ℝ) + 1) ^ (k + 2) *
        exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))) t := by
  convert! ((hasDerivAt_id t).const_mul (-Real.pi * ((n : ℝ) + 1) ^ 2)).exp.const_mul
    (((n : ℝ) + 1) ^ k) using 1 <;> simp only [pow_add, id_eq, mul_one] <;> ring

/-- Termwise differentiation is justified by the explicit local majorant. -/
theorem hasDerivAt_thetaSeries (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (thetaSeries k) (-Real.pi * thetaSeries (k + 2) t) t := by
  obtain ⟨hs, hb⟩ := thetaSeries_local_majorant k (half_pos ht)
  have h := hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioi (convex_Ioi (t / 2)).isPreconnected
    (fun n y _ => term_hasDerivAt k n y)
    (fun n y hy => hb n y (le_of_lt hy))
    (show t ∈ Ioi (t / 2) by simp only [mem_Ioi]; linarith)
    (thetaSeries_summable k ht)
    (show t ∈ Ioi (t / 2) by simp only [mem_Ioi]; linarith)
  simpa only [thetaSeries, tsum_mul_left] using! h

/-- The zeroth weighted series is exactly half of the actual theta tail. -/
theorem thetaSeries_zero {t : ℝ} (ht : 0 < t) :
    thetaSeries 0 t = (theta t - 1) / 2 := by
  have h := (HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht).mul_left (1 / 2 : ℝ)
  simp only [mul_zero, zero_mul, cos_zero, mul_one] at h
  have h' : HasSum (fun n : ℕ => exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
      ((theta t - 1) / 2) := by
    simpa only [theta, HurwitzZeta.evenKernel_eq_cosKernel_of_zero, ← mul_assoc,
      one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul, div_eq_mul_inv, AddCircle.coe_zero,
      mul_comm] using! h
  simpa only [thetaSeries, pow_zero, one_mul] using h'.tsum_eq

/-- The rescaled theta tail has its literal positive-index series representation. -/
theorem psi_eq_series (x : ℝ) : psi x = exp (x / 2) * thetaSeries 0 (exp (2 * x)) := by
  rw [thetaSeries_zero (exp_pos _), psi, mul_div_assoc]

/-- The original differential weight expressed in two convergent weighted series. -/
theorem omega_eq_series {t : ℝ} (ht : 0 < t) :
    omega t = 2 * Real.pi ^ 2 * t ^ 2 * thetaSeries 4 t -
      3 * Real.pi * t * thetaSeries 2 t := by
  unfold omega thetaSeries
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_sub ((thetaSeries_summable 4 ht).mul_left _)
      ((thetaSeries_summable 2 ht).mul_left _)]
  apply tsum_congr
  intro n
  push_cast
  ring

/-- The first derivative written with the zeroth and second theta weights. -/
def psiFirst (x : ℝ) : ℝ := exp (x / 2) *
  (thetaSeries 0 (exp (2 * x)) / 2 - 2 * Real.pi * exp (2 * x) * thetaSeries 2 (exp (2 * x)))

/-- The second derivative written with the first three even theta weights. -/
def psiSecond (x : ℝ) : ℝ := exp (x / 2) *
  (thetaSeries 0 (exp (2 * x)) / 4 - 6 * Real.pi * exp (2 * x) * thetaSeries 2 (exp (2 * x)) +
    4 * Real.pi ^ 2 * exp (2 * x) ^ 2 * thetaSeries 4 (exp (2 * x)))

private theorem exp_half_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => exp (x / 2)) (exp (x / 2) / 2) x := by
  convert! ((hasDerivAt_id x).div_const 2).exp using 1 <;> simp <;> ring

private theorem exp_twice_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => exp (2 * x)) (2 * exp (2 * x)) x := by
  convert! ((hasDerivAt_id x).const_mul 2).exp using 1 <;> simp <;> ring

private theorem composed_series_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => thetaSeries k (exp (2 * x)))
      (-2 * Real.pi * exp (2 * x) * thetaSeries (k + 2) (exp (2 * x))) x := by
  convert! (hasDerivAt_thetaSeries k (exp_pos (2 * x))).comp x (exp_twice_deriv x) using 1 <;> ring

/-- The first derivative of the original rescaled theta tail. -/
theorem hasDerivAt_psi (x : ℝ) : HasDerivAt psi (psiFirst x) x := by
  rw [show psi = fun x => exp (x / 2) * thetaSeries 0 (exp (2 * x)) from funext psi_eq_series]
  convert! (exp_half_deriv x).mul (composed_series_deriv 0 x) using 1
  simp only [psiFirst]
  ring

/-- The second differentiation uses the same proved local majorants. -/
theorem hasDerivAt_psiFirst (x : ℝ) : HasDerivAt psiFirst (psiSecond x) x := by
  have h0 := composed_series_deriv 0 x
  have h2 := composed_series_deriv 2 x
  convert! (exp_half_deriv x).mul ((h0.div_const 2).sub
    (((exp_twice_deriv x).const_mul (2 * Real.pi)).mul h2)) using 1
  simp only [psiSecond, Pi.sub_apply, Pi.mul_apply]
  ring

/-- The differential operator applied to the actual theta tail gives Romik's kernel. -/
theorem romikPhi_eq_differential (x : ℝ) :
    romikPhi x = deriv (deriv psi) x - psi x / 4 := by
  have hd : deriv psi = psiFirst := funext (fun y => (hasDerivAt_psi y).deriv)
  rw [hd, (hasDerivAt_psiFirst x).deriv, romikPhi, omega_eq_series (exp_pos _),
    psi_eq_series, psiSecond]
  ring

/-- The theta functional equation after the logarithmic substitution. -/
theorem theta_exp_neg (x : ℝ) : theta (exp (2 * -x)) = exp x * theta (exp (2 * x)) := by
  have h := HurwitzZeta.evenKernel_functional_equation (0 : UnitAddCircle) (exp (2 * -x))
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, ← exp_mul] at h
  have h1 : 2 * -x * (1 / 2 : ℝ) = -x := by ring
  have h2 : 1 / exp (2 * -x) = exp (2 * x) := by
    rw [one_div, ← exp_neg]
    congr 1
    ring
  rw [h1, h2] at h
  simpa only [theta, one_div, ← exp_neg, neg_neg] using! h

/-- The nonsymmetric theta tail has an explicit elementary reflection defect. -/
theorem psi_reflection (x : ℝ) :
    psi (-x) = psi x + (exp (x / 2) - exp (-x / 2)) / 2 := by
  unfold psi
  rw [theta_exp_neg]
  have h : exp (-x / 2) * exp x = exp (x / 2) := by
    rw [← exp_add]
    congr 1
    ring
  linear_combination (theta (exp (2 * x)) / 2) * h

/-- Differentiating the modular reflection identity once. -/
theorem psiFirst_reflection (x : ℝ) :
    psiFirst (-x) = -psiFirst x - (exp (x / 2) + exp (-x / 2)) / 4 := by
  have hl := (hasDerivAt_psi (-x)).comp x (hasDerivAt_neg x)
  have he := (exp_half_deriv (-x)).comp x (hasDerivAt_neg x)
  have hr := (hasDerivAt_psi x).add (((exp_half_deriv x).sub he).div_const 2)
  have hf : (fun x => psi (-x)) = (fun x => psi x + (exp (x / 2) - exp (-x / 2)) / 2) :=
    funext psi_reflection
  change HasDerivAt (fun x => psi (-x)) _ x at hl
  rw [hf] at hl
  have h := hl.unique hr
  linarith

/-- The boundary derivative is fixed by modular theta, with no normalization premise. -/
theorem psi_deriv_zero : deriv psi 0 = -1 / 4 := by
  rw [(hasDerivAt_psi 0).deriv]
  have h := psiFirst_reflection 0
  norm_num at h ⊢
  linarith

/-- Differentiating the modular reflection identity twice. -/
theorem psiSecond_reflection (x : ℝ) :
    psiSecond (-x) = psiSecond x + (exp (x / 2) - exp (-x / 2)) / 8 := by
  have hl := (hasDerivAt_psiFirst (-x)).comp x (hasDerivAt_neg x)
  have he := (exp_half_deriv (-x)).comp x (hasDerivAt_neg x)
  have hr := (hasDerivAt_psiFirst x).neg.sub (((exp_half_deriv x).add he).div_const 4)
  have hf : (fun x => psiFirst (-x)) =
      (fun x => -psiFirst x - (exp (x / 2) + exp (-x / 2)) / 4) := funext psiFirst_reflection
  change HasDerivAt (fun x => psiFirst (-x)) _ x at hl
  rw [hf] at hl
  have h := hl.unique hr
  linarith

/-- Evenness is a consequence of modular differentiation, not part of the definition. -/
theorem romikPhi_even (x : ℝ) : romikPhi (-x) = romikPhi x := by
  have hd : deriv psi = psiFirst := funext (fun y => (hasDerivAt_psi y).deriv)
  simp only [romikPhi_eq_differential, hd, (hasDerivAt_psiFirst _).deriv,
    psiSecond_reflection, psi_reflection]
  ring

private theorem romikPhi_eq_source_nonneg {x : ℝ} (hx : 0 ≤ x) :
    romikPhi x = sourceThetaKernel x := by
  unfold romikPhi omega sourceThetaKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [abs_of_nonneg hx]
  have h9 : exp (9 * x / 2) = exp (x / 2) * exp (2 * x) ^ 2 := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    ring
  have h5 : exp (5 * x / 2) = exp (x / 2) * exp (2 * x) := by
    rw [← exp_add]
    congr 1
    ring
  rw [h9, h5]
  ring

/-- Identification with the fixed theta kernel on the entire real axis. -/
theorem romikPhi_eq_source (x : ℝ) : romikPhi x = sourceThetaKernel x := by
  rcases le_or_gt 0 x with hx | hx
  · exact romikPhi_eq_source_nonneg hx
  · rw [← romikPhi_even x, romikPhi_eq_source_nonneg (by linarith)]
    exact D5.S3.Zeros.Jensen.SourceThetaMomentBounds.source_theta_even x

private theorem thetaSeries_nonneg (k : ℕ) (t : ℝ) : 0 ≤ thetaSeries k t := by
  unfold thetaSeries
  exact tsum_nonneg (fun n => by positivity)

private theorem thetaSeries_le_next (k : ℕ) {t : ℝ} (ht : 0 < t) :
    thetaSeries k t ≤ thetaSeries (k + 2) t := by
  apply Summable.tsum_le_tsum _ (thetaSeries_summable k ht) (thetaSeries_summable (k + 2) ht)
  intro n
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 1) (by omega)

/-- The theta tail and its first derivative are dominated by the positive kernel on the ray. -/
theorem psi_bounds {x : ℝ} (hx : 0 ≤ x) :
    |psi x| ≤ sourceThetaKernel x ∧ |psiFirst x| ≤ sourceThetaKernel x := by
  let t := exp (2 * x)
  let p := Real.pi * t
  have ht : 0 < t := exp_pos _
  have ht1 : 1 ≤ t := one_le_exp (by linarith)
  have hp : 3 ≤ p := by
    dsimp [p]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) Real.pi_pos.le, Real.pi_gt_three]
  have h0 := thetaSeries_nonneg 0 t
  have h2 := thetaSeries_nonneg 2 t
  have h4 := thetaSeries_nonneg 4 t
  have h02 := thetaSeries_le_next 0 ht
  have h24 := thetaSeries_le_next 2 ht
  norm_num only at h02 h24
  have hc : 2 * p * thetaSeries 2 t ≥ thetaSeries 0 t / 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * p - 1) h2]
  have hpoly : 1 + 2 * p ≤ 4 * p ^ 2 - 6 * p := by nlinarith
  have hcoeff : (1 + 2 * p) * thetaSeries 2 t ≤
      4 * p ^ 2 * thetaSeries 4 t - 6 * p * thetaSeries 2 t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h24) (sq_nonneg p),
      mul_nonneg (sub_nonneg.mpr hpoly) h2]
  have hk : sourceThetaKernel x = exp (x / 2) *
      (4 * p ^ 2 * thetaSeries 4 t - 6 * p * thetaSeries 2 t) := by
    rw [← romikPhi_eq_source, romikPhi, omega_eq_series ht]
    dsimp [p, t]
    ring
  rw [hk, psi_eq_series, psiFirst]
  rw [show 2 * Real.pi * exp (2 * x) = 2 * p by dsimp [p, t]; ring]
  change |exp (x / 2) * thetaSeries 0 t| ≤ _ ∧
    |exp (x / 2) * (thetaSeries 0 t / 2 - 2 * p * thetaSeries 2 t)| ≤ _
  rw [abs_of_nonneg (mul_nonneg (exp_pos _).le h0),
    abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith))]
  constructor
  · apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    nlinarith [mul_nonneg (by linarith : 0 ≤ p) h2]
  · rw [← mul_neg]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    linarith

end D5.S3.Analytic.Fourier.ThetaDifferentialKernel
