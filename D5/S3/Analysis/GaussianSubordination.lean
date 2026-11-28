/- GID: D5/S3/Analysis/GaussianSubordination
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-mass-shell4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Gaussian subordination integral on the positive half-line follows from the Gaussian integral under `x ↦ wx - b/x`, with the two terms of the Jacobian related by reciprocal substitution. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
Omega original.

The Gaussian subordination integral on the positive half-line follows from
the Gaussian integral under `x ↦ wx - b/x`, with the two terms of the
Jacobian related by reciprocal substitution.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace Omega

/-- Reciprocal substitution with positive numerator on the positive half-line. -/
theorem integral_Ioi_const_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) (f : ℝ → E) :
    (∫ x in Ioi (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), (c / x ^ 2) • f (c / x) := by
  have hinv (x : ℝ) (hx : 0 < x) : c / (c / x) = x := by
    field_simp
  have himage : (fun x : ℝ => c / x) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact div_pos hc hy
    · intro hx
      exact ⟨c / x, div_pos hc hx, hinv x hx⟩
  have hinj : InjOn (fun x : ℝ => c / x) (Ioi 0) := by
    intro x hx y hy h
    change c / x = c / y at h
    rw [← hinv x hx, ← hinv y hy, h]
  have hderiv (x : ℝ) (hx : x ∈ Ioi 0) :
      HasDerivWithinAt (fun x : ℝ => c / x) (-(c / x ^ 2)) (Ioi 0) x := by
    have h := (hasDerivAt_const x c).div (hasDerivAt_id' x) (ne_of_gt hx)
    simpa only [Pi.div_def, zero_mul, mul_one, zero_sub, neg_div] using h.hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj f
  rw [himage] at h
  refine h.trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change |-(c / x ^ 2)| • f (c / x) = (c / x ^ 2) • f (c / x)
  rw [abs_neg, abs_of_nonneg (by positivity)]

private def gaussianCoordinate (w b x : ℝ) : ℝ := w * x - b / x

private theorem gaussianCoordinate_deriv (w b : ℝ) (x : ℝ) (hx : x ∈ Ioi 0) :
    HasDerivWithinAt (gaussianCoordinate w b) (w + b / x ^ 2) (Ioi 0) x := by
  have h := ((hasDerivAt_id' x).const_mul w).sub
    ((hasDerivAt_const x b).div (hasDerivAt_id' x) (ne_of_gt hx))
  unfold gaussianCoordinate
  simpa only [Pi.div_def, Pi.sub_def, mul_one, zero_mul, zero_sub,
    neg_div, sub_neg_eq_add] using h.hasDerivWithinAt

private theorem gaussianCoordinate_injOn {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    InjOn (gaussianCoordinate w b) (Ioi 0) := by
  apply StrictMonoOn.injOn
  intro x hx y hy hxy
  have hdiv : b / y ≤ b / x := div_le_div_of_nonneg_left hb.le hx hxy.le
  unfold gaussianCoordinate
  linarith [mul_lt_mul_of_pos_left hxy hw]

private theorem gaussianCoordinate_image {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    gaussianCoordinate w b '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro y
  let d := √(y ^ 2 + 4 * w * b)
  let x := (y + d) / (2 * w)
  have hd : d ^ 2 = y ^ 2 + 4 * w * b := Real.sq_sqrt (by positivity)
  have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
  have hwb : 0 < w * b := mul_pos hw hb
  have hxd : 0 < y + d := by
    by_contra! h
    have hsq := pow_le_pow_left₀ hd_nonneg (show d ≤ -y by linarith) (2 : ℕ)
    nlinarith
  have hx : 0 < x := div_pos hxd (by positivity)
  have hquad : w * x ^ 2 - y * x - b = 0 := by
    dsimp only [x]
    field_simp
    linear_combination hd
  refine ⟨x, hx, ?_⟩
  unfold gaussianCoordinate
  field_simp
  nlinarith

private theorem gaussianCoordinate_integral {w b : ℝ} (hw : 0 < w) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.exp (-(gaussianCoordinate w b x) ^ 2)) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(gaussianCoordinate w b x) ^ 2)) =
      Real.sqrt Real.pi / (2 * w) := by
  let g : ℝ → ℝ := fun x => Real.exp (-x ^ 2)
  let G := g ∘ gaussianCoordinate w b
  let J : ℝ → ℝ := fun x => w + b / x ^ 2
  have hJ (x : ℝ) (_hx : x ∈ Ioi 0) : 0 ≤ J x := by
    dsimp [J]
    positivity
  have hJac :
      (∫ x, g x) = ∫ x in Ioi (0 : ℝ), J x * G x := by
    have h := integral_image_eq_integral_abs_deriv_smul (f := gaussianCoordinate w b)
      measurableSet_Ioi (gaussianCoordinate_deriv w b) (gaussianCoordinate_injOn hw hb) g
    rw [gaussianCoordinate_image hw hb, setIntegral_univ] at h
    refine h.trans (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_)
    change |J x| * G x = J x * G x
    rw [abs_of_nonneg (hJ x hx)]
  have hg : Integrable g := by
    simpa [g] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hInt : IntegrableOn (fun x => J x * G x) (Ioi 0) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f := gaussianCoordinate w b)
      measurableSet_Ioi (gaussianCoordinate_deriv w b) (gaussianCoordinate_injOn hw hb) g).1
      (hg.integrableOn : IntegrableOn g _)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change |J x| * G x = J x * G x
    rw [abs_of_nonneg (hJ x hx)]
  have h1 : IntegrableOn (fun x => w * G x) (Ioi 0) := by
    refine hInt.mono' (by dsimp [G, g, gaussianCoordinate]; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hG : 0 ≤ G x := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg (mul_nonneg hw.le hG)]
    apply mul_le_mul_of_nonneg_right _ hG
    dsimp [J]
    have : 0 ≤ b / x ^ 2 := by positivity
    linarith
  have h2 : IntegrableOn (fun x => (b / x ^ 2) * G x) (Ioi 0) := by
    convert hInt.sub h1 using 1
    funext x
    dsimp [J]
    ring
  have hEq : (∫ x in Ioi (0 : ℝ), w * G x) = ∫ x in Ioi (0 : ℝ), (b / x ^ 2) * G x := by
    refine (integral_Ioi_const_div (div_pos hb hw) (fun x => w * G x)).trans ?_
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := hx
    have href : gaussianCoordinate w b ((b / w) / x) = -gaussianCoordinate w b x := by
      unfold gaussianCoordinate
      field_simp
      ring
    change (b / w / x ^ 2) * (w * g (gaussianCoordinate w b (b / w / x))) =
      b / x ^ 2 * g (gaussianCoordinate w b x)
    rw [href]
    dsimp [g]
    rw [neg_sq]
    field_simp
  have hsplit : (∫ x in Ioi (0 : ℝ), J x * G x) =
      (∫ x in Ioi (0 : ℝ), w * G x) + ∫ x in Ioi (0 : ℝ), (b / x ^ 2) * G x := by
    simp_rw [J, add_mul]
    exact integral_add h1 h2
  have hvalue : (∫ x, g x) = Real.sqrt Real.pi := by simpa [g] using integral_gaussian 1
  rw [hJac, hsplit, ← hEq, integral_const_mul] at hvalue
  constructor
  · change Integrable (fun x => G x) (volume.restrict (Ioi (0 : ℝ)))
    simpa only [← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul] using h1.const_mul w⁻¹
  apply (eq_div_iff (by positivity : 2 * w ≠ 0)).2
  change (∫ x in Ioi (0 : ℝ), G x) * (2 * w) = _
  linarith

private theorem subordination_integrability_and_value {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * Real.exp (-(w ^ 2 * s) - t ^ 2 / (4 * s)))
      (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), s ^ (-(1/2) : ℝ) * Real.exp (-(w ^ 2 * s) - t ^ 2 / (4 * s))) =
      Real.sqrt Real.pi * Real.exp (-t * w) / w := by
  let F : ℝ → ℝ := fun s => s ^ (-(1/2) : ℝ) * Real.exp (-(w ^ 2 * s) - t ^ 2 / (4 * s))
  have hderiv (x : ℝ) (_hx : x ∈ Ioi 0) :
      HasDerivWithinAt (fun y : ℝ => y ^ 2) (2 * x) (Ioi 0) x := by
    simpa [Pi.pow_def] using ((hasDerivAt_id' x).pow 2).hasDerivWithinAt
  have hinj : InjOn (fun y : ℝ => y ^ 2) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro x hx y hy hxy
    exact pow_lt_pow_left₀ hxy hx.le (by norm_num)
  have himage : (fun y : ℝ => y ^ 2) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, (hx : 0 < x), rfl⟩
      exact pow_pos hx _
    · intro hy
      exact ⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩
  let b := t / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hrel (x : ℝ) (hx : x ∈ Ioi 0) :
      |2 * x| • F (x ^ 2) =
        (2 * Real.exp (-t * w)) * Real.exp (-(gaussianCoordinate w b x) ^ 2) := by
    have hx' : 0 < x := hx
    change |2 * x| * F (x ^ 2) = _
    have hpow : (x ^ 2) ^ (-(1/2) : ℝ) = x⁻¹ := by
      rw [Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx'.le]
    have hexp : -(w ^ 2 * x ^ 2) - t ^ 2 / (4 * x ^ 2) =
        -t * w + -(gaussianCoordinate w b x) ^ 2 := by
      dsimp [gaussianCoordinate, b]
      field_simp
      ring
    dsimp only [F]
    rw [abs_of_nonneg (by positivity), hpow, hexp, Real.exp_add]
    field_simp
  obtain ⟨hg, hvalue⟩ := gaussianCoordinate_integral hw hb
  constructor
  · have htarget := (hg.const_mul (2 * Real.exp (-t * w))).congr
      (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => (hrel x hx).symm)
    rw [← himage]
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj F).2
      htarget
  · change (∫ s in Ioi (0 : ℝ), F s) = _
    calc
      _ = ∫ x in (fun y : ℝ => y ^ 2) '' Ioi 0, F x := by rw [himage]
      _ = ∫ x in Ioi (0 : ℝ), |2 * x| • F (x ^ 2) :=
        integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
      _ = _ := by
        rw [setIntegral_congr_fun measurableSet_Ioi hrel, integral_const_mul, hvalue]
        field_simp

/-- The Gaussian subordination integrand is integrable for positive parameters. -/
theorem integrableOn_gaussian_subordination {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ) * Real.exp (-(w ^ 2 * s) - t ^ 2 / (4 * s)))
      (Ioi 0) :=
  (subordination_integrability_and_value hw ht).1

/-- The regulated inverse energy is an integral of Gaussian heat kernels. -/
theorem gaussian_subordination {w t : ℝ} (hw : 0 < w) (ht : 0 < t) :
    Real.exp (-t * w) / (2 * w) =
      (1 / (2 * Real.sqrt Real.pi)) *
        ∫ s in Ioi (0 : ℝ), s ^ (-(1/2) : ℝ) * Real.exp (-(w ^ 2 * s) - t ^ 2 / (4 * s)) := by
  rw [(subordination_integrability_and_value hw ht).2]
  have hpi : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

end Omega
