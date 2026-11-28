/- GID: D5/S3/MeasureTheory/RealAffineRepresentation
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The real affine group in exponential coordinates acts by weighted pullback on Lebesgue square-integrable functions. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Omega original.

The real affine group in exponential coordinates acts by weighted pullback
on Lebesgue square-integrable functions. Its Lie action on Schwartz functions
fixes the sign relating modular dilations to the positive-frequency multiplier.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.RealAffine

open MeasureTheory
open scoped NNReal ENNReal SchwartzMap FourierTransform

/-- Affine parameters in exponential dilation coordinates. -/
@[ext]
structure Affine (c : ℝ) where
  s : ℝ
  a : ℝ

variable {c : ℝ}

/-- The positive slope of an affine transformation. -/
def scale (g : Affine c) : ℝ := Real.exp (c * g.s)

theorem scale_pos (g : Affine c) : 0 < scale g := Real.exp_pos _

private theorem exp_mul_add (c s t : ℝ) :
    Real.exp (c * (s + t)) = Real.exp (c * s) * Real.exp (c * t) := by
  rw [mul_add, Real.exp_add]

instance : Group (Affine c) where
  one := ⟨0, 0⟩
  mul g h := ⟨g.s + h.s, g.a + scale g * h.a⟩
  inv g := ⟨-g.s, -g.a / scale g⟩
  one_mul g := by
    ext
    · exact zero_add _
    · change (0 : ℝ) + Real.exp (c * 0) * g.a = g.a
      simp
  mul_one g := by
    ext
    · exact add_zero _
    · change g.a + scale g * 0 = g.a
      simp
  mul_assoc g h k := by
    ext
    · exact add_assoc _ _ _
    · change g.a + scale g * h.a + Real.exp (c * (g.s + h.s)) * k.a =
        g.a + scale g * (h.a + scale h * k.a)
      rw [exp_mul_add]
      unfold scale
      ring
  inv_mul_cancel g := by
    have hn := (scale_pos g).ne'
    ext
    · exact neg_add_cancel _
    · change -g.a / scale g + Real.exp (c * -g.s) * g.a = 0
      rw [mul_neg, Real.exp_neg]
      change -g.a / scale g + (scale g)⁻¹ * g.a = 0
      field_simp
      ring

theorem mul_coordinates (g h : Affine c) :
    g * h = ⟨g.s + h.s, g.a + scale g * h.a⟩ := rfl

@[simp] theorem scale_mul (g h : Affine c) : scale (g * h) = scale g * scale h :=
  exp_mul_add c g.s h.s

private theorem scale_one : scale (1 : Affine c) = 1 := by
  simp [scale, show (1 : Affine c).s = 0 from rfl]

/-- Dilation subgroup. -/
def dilation (c s : ℝ) : Affine c := ⟨s, 0⟩

/-- Translation subgroup. -/
def translation (c a : ℝ) : Affine c := ⟨0, a⟩

theorem conj_translation (s a : ℝ) :
    dilation c s * translation c a * (dilation c s)⁻¹ =
      translation c (Real.exp (c * s) * a) := by
  ext
  · change s + 0 + -s = 0
    ring
  · change 0 + scale (dilation c s) * a +
      scale (dilation c s * translation c a) * (-0 / scale (dilation c s)) = _
    simp [scale, dilation, translation]

private def matrix (g : Affine c) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![scale g, g.a; 0, 1]

private theorem matrix_one : matrix (1 : Affine c) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, scale_one, show (1 : Affine c).a = 0 from rfl]

private theorem matrix_mul (g h : Affine c) : matrix (g * h) = matrix g * matrix h := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_two, mul_coordinates, add_comm]
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The faithful upper triangular matrix representation when the dilation rate is nonzero. -/
def affineMatrix (c : ℝ) : Affine c →* (Matrix (Fin 2) (Fin 2) ℝ)ˣ where
  toFun g :=
    ⟨matrix g, matrix g⁻¹,
      by rw [← matrix_mul, mul_inv_cancel, matrix_one],
      by rw [← matrix_mul, inv_mul_cancel, matrix_one]⟩
  map_one' := Units.ext matrix_one
  map_mul' g h := Units.ext (matrix_mul g h)

theorem affineMatrix_injective (hc : c ≠ 0) : Function.Injective (affineMatrix c) := by
  intro g h hgh
  have hm := congrArg (fun u : (Matrix (Fin 2) (Fin 2) ℝ)ˣ => u.val) hgh
  have hs : scale g = scale h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 0) hm
  ext
  · exact mul_left_cancel₀ hc (Real.exp_injective hs)
  · exact congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 1) hm

/-- The pullback coordinate for the affine action on functions. -/
def coord (g : Affine c) (x : ℝ) : ℝ := (x + g.a) / scale g

private theorem coord_measurable (g : Affine c) : Measurable (coord g) := by
  unfold coord
  fun_prop

theorem affine_map_volume (g : Affine c) :
    Measure.map (coord g) volume = ENNReal.ofReal (scale g) • (volume : Measure ℝ) := by
  have hs := (scale_pos g).ne'
  have hmeas : Measurable (fun x : ℝ => (scale g)⁻¹ * x) := by fun_prop
  rw [show coord g = ((fun x : ℝ => (scale g)⁻¹ * x) ∘ (fun x : ℝ => x + g.a)) by
    ext x
    simp [coord, div_eq_inv_mul]]
  rw [← Measure.map_map hmeas (by fun_prop), (measurePreserving_add_right volume g.a).map_eq,
    Real.map_volume_mul_left (inv_ne_zero hs), inv_inv, abs_of_pos (scale_pos g)]

private theorem pullAE (g : Affine c) {p : ℝ → Prop}
    (h : ∀ᵐ x ∂volume, p x) : ∀ᵐ x ∂volume, p (coord g x) := by
  have hq : QuasiMeasurePreserving (coord g) volume volume := by
    refine ⟨coord_measurable g, ?_⟩
    rw [affine_map_volume]
    exact Measure.AbsolutelyContinuous.smul_left .rfl _
  exact hq.tendsto_ae.eventually h

/-- The complex Hilbert space of Lebesgue-square-integrable functions on the real line. -/
abbrev PositionL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The weight compensating for the inverse-coordinate Jacobian. -/
def weight (g : Affine c) : ℂ := (Real.exp (-(c * g.s) / 2) : ℂ)

private theorem sqrt_scale (g : Affine c) :
    Real.sqrt (scale g) = Real.exp (c * g.s / 2) := by
  rw [Real.sqrt_eq_rpow, scale, ← Real.exp_mul]
  congr 1
  ring

theorem weight_eq (g : Affine c) : weight g = ((Real.sqrt (scale g))⁻¹ : ℝ) := by
  unfold weight
  rw [sqrt_scale, ← Real.exp_neg]
  congr 2
  ring

private theorem weight_mul (g h : Affine c) : weight (g * h) = weight g * weight h := by
  change (Real.exp (-(c * (g.s + h.s)) / 2) : ℂ) = _
  rw [show -(c * (g.s + h.s)) / 2 = -(c * g.s) / 2 + -(c * h.s) / 2 by ring,
    Real.exp_add, Complex.ofReal_mul]
  rfl

private theorem coord_mul (g h : Affine c) (x : ℝ) :
    coord (g * h) x = coord h (coord g x) := by
  have hg := (scale_pos g).ne'
  have hh := (scale_pos h).ne'
  simp only [coord, scale_mul]
  change (x + (g.a + scale g * h.a)) / (scale g * scale h) =
    ((x + g.a) / scale g + h.a) / scale h
  field_simp
  ring

private theorem memLp_comp (g : Affine c) (f : PositionL2) :
    MemLp (fun x => f (coord g x)) 2 volume := by
  apply MemLp.comp_of_map _ (coord_measurable g).aemeasurable
  rw [affine_map_volume]
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

private def pull (g : Affine c) (f : PositionL2) : PositionL2 :=
  weight g • (memLp_comp g f).toLp _

private theorem pull_ae (g : Affine c) (f : PositionL2) :
    ⇑(pull g f) =ᵐ[volume] fun x => weight g * f (coord g x) := by
  filter_upwards [Lp.coeFn_smul (weight g) ((memLp_comp g f).toLp _),
    MemLp.coeFn_toLp (memLp_comp g f)] with x h₁ h₂
  simpa [pull, h₂, smul_eq_mul] using h₁

private theorem norm_pull (g : Affine c) (f : PositionL2) : ‖pull g f‖ = ‖f‖ := by
  have hf : AEStronglyMeasurable f (Measure.map (coord g) volume) := by
    rw [affine_map_volume]
    exact (Lp.aestronglyMeasurable f).smul_measure _
  have hs := (scale_pos g).le
  rw [pull, norm_smul, Lp.norm_toLp]
  change ‖weight g‖ * (eLpNorm (f ∘ coord g) 2 volume).toReal = ‖f‖
  rw [← eLpNorm_map_measure (p := 2) hf (coord_measurable g).aemeasurable,
    affine_map_volume, eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hs]
  have hExp : ((1 / (2 : ℝ≥0∞)).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [hExp, ← Real.sqrt_eq_rpow, weight_eq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), ← Lp.norm_def, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (scale_pos g)).ne', one_mul]

private def pullLinear (g : Affine c) : PositionL2 →ₗᵢ[ℂ] PositionL2 where
  toFun := pull g
  map_add' f h := by
    apply Lp.ext
    filter_upwards [pull_ae g (f + h), pull_ae g f, pull_ae g h,
      pullAE g (Lp.coeFn_add f h), Lp.coeFn_add (pull g f) (pull g h)]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₅, h₂, h₃, h₄, mul_add]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [pull_ae g (z • f), pull_ae g f, pullAE g (Lp.coeFn_smul z f),
      Lp.coeFn_smul z (pull g f)] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
    rw [RingHom.id_apply, h₁, h₄, h₂, h₃]
    ring
  norm_map' := norm_pull g

private theorem pull_one (f : PositionL2) : pull (1 : Affine c) f = f := by
  apply Lp.ext
  filter_upwards [pull_ae (1 : Affine c) f] with x hx
  simpa [weight, coord, scale_one, show (1 : Affine c).s = 0 from rfl,
    show (1 : Affine c).a = 0 from rfl] using hx

private theorem pull_mul (g h : Affine c) (f : PositionL2) :
    pull (g * h) f = pull g (pull h f) := by
  apply Lp.ext
  filter_upwards [pull_ae (g * h) f, pull_ae g (pull h f), pullAE g (pull_ae h f)]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, weight_mul, coord_mul, mul_assoc]

private def pullEquiv (g : Affine c) : PositionL2 ≃ₗᵢ[ℂ] PositionL2 :=
  LinearIsometryEquiv.ofSurjective (pullLinear g) fun f =>
    ⟨pull g⁻¹ f, by
      change pull g (pull g⁻¹ f) = f
      rw [← pull_mul, mul_inv_cancel, pull_one]⟩

/-- The unitary representation by inverse affine coordinate and its square-root Jacobian. -/
def affineUnitary (c : ℝ) : Affine c →* (PositionL2 ≃ₗᵢ[ℂ] PositionL2) where
  toFun := pullEquiv
  map_one' := LinearIsometryEquiv.ext pull_one
  map_mul' g h := LinearIsometryEquiv.ext (pull_mul g h)

theorem affineUnitary_ae (g : Affine c) (f : PositionL2) :
    ⇑(affineUnitary c g f) =ᵐ[volume]
      fun x => ((Real.sqrt (scale g))⁻¹ : ℝ) * f ((x + g.a) / scale g) := by
  change ⇑(pullEquiv g f) =ᵐ[volume] _
  rw [show pullEquiv g f = pull g f by simp [pullEquiv, pullLinear]]
  simpa only [weight_eq, coord] using pull_ae g f

/-- The real frequency multiplier for the translation generator. -/
def frequency (ξ : ℝ) : ℝ := 2 * Real.pi * ξ

/-- Translation energy on Schwartz frequency vectors. -/
def schwartzP (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 * (Real.pi : ℂ)) • SchwartzMap.smulLeftCLM ℂ Complex.ofReal f

/-- Dilation generator on Schwartz frequency vectors, with time evolution `exp (-isK)`. -/
def schwartzK (c : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (Complex.I * (c : ℂ)) •
    (SchwartzMap.smulLeftCLM ℂ Complex.ofReal (SchwartzMap.derivCLM ℂ ℂ f) + (1 / 2 : ℂ) • f)

theorem schwartzP_apply (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    schwartzP f ξ = (frequency ξ : ℂ) * f ξ := by
  simp only [schwartzP, smul_apply, SchwartzMap.smulLeftCLM_apply_apply
    Complex.hasTemperateGrowth_ofReal, smul_eq_mul, frequency, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem schwartzK_apply (c : ℝ) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    schwartzK c f ξ = Complex.I * (c : ℂ) * ((ξ : ℂ) * deriv f ξ + f ξ / 2) := by
  simp only [schwartzK, smul_apply, add_apply, SchwartzMap.smulLeftCLM_apply_apply
    Complex.hasTemperateGrowth_ofReal, SchwartzMap.derivCLM_apply, smul_eq_mul, div_eq_inv_mul]
  ring

private theorem hasDerivAt_schwartzP (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    HasDerivAt (schwartzP f) (2 * (Real.pi : ℂ) * (f ξ + (ξ : ℂ) * deriv f ξ)) ξ := by
  have h := ((hasDerivAt_id ξ).ofReal_comp.mul (f.differentiableAt.hasDerivAt)).const_mul
    (2 * (Real.pi : ℂ))
  convert h using 1
  · funext x
    simp [schwartzP_apply, frequency, mul_assoc]
  · simp only [Complex.ofReal_one, id_eq, one_mul]

/-- The commutator on the common invariant Schwartz domain. -/
theorem schwartz_bracket (c : ℝ) (f : 𝓢(ℝ, ℂ)) :
    schwartzK c (schwartzP f) - schwartzP (schwartzK c f) =
      (Complex.I * (c : ℂ)) • schwartzP f := by
  ext ξ
  simp only [sub_apply, smul_apply, smul_eq_mul, schwartzK_apply,
    schwartzP_apply, (hasDerivAt_schwartzP f ξ).deriv, frequency, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

/-- Minus-sided modular time gives the coefficient `-2πi`. -/
theorem schwartz_minus_bracket (f : 𝓢(ℝ, ℂ)) :
    schwartzK (-2 * Real.pi) (schwartzP f) - schwartzP (schwartzK (-2 * Real.pi) f) =
      (-2 * (Real.pi : ℂ) * Complex.I) • schwartzP f := by
  rw [schwartz_bracket]
  congr 1
  push_cast
  ring

/-- Positive frequency is preserved by both Schwartz generators. -/
theorem schwartz_positiveFrequency_invariant (f : 𝓢(ℝ, ℂ))
    (hf : ∀ ξ < 0, f ξ = 0) (ξ : ℝ) (hξ : ξ < 0) :
    schwartzP f ξ = 0 ∧ schwartzK c f ξ = 0 := by
  have hn : f =ᶠ[nhds ξ] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hξ] with x hx
    exact hf x hx
  have hd : deriv f ξ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hn, deriv_const]
  simp [schwartzP_apply, schwartzK_apply, hf ξ hξ, hd]

theorem frequency_nonneg {ξ : ℝ} (hξ : 0 ≤ ξ) : 0 ≤ frequency ξ :=
  mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hξ

theorem range_frequency_nonneg :
    frequency '' Set.Ici 0 = Set.Ici 0 := by
  have h : 0 < 2 * Real.pi := by positivity
  ext x
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact frequency_nonneg hξ
  · intro hx
    refine ⟨x / (2 * Real.pi), div_nonneg hx h.le, ?_⟩
    unfold frequency
    field_simp

/-- The Fourier phase of a translation by `a` in pullback coordinates. -/
def phase (a ξ : ℝ) : ℂ := Complex.exp (((a * frequency ξ : ℝ) : ℂ) * Complex.I)

private theorem phase_norm (a ξ : ℝ) : ‖phase a ξ‖ = 1 := by simp [phase, Complex.norm_exp]

private theorem coord_anti (g : Affine c) :
    AntilipschitzWith ⟨scale g, (scale_pos g).le⟩ (coord g) := by
  have hs := (scale_pos g).ne'
  intro x y
  have hdist : dist x y = scale g * dist (coord g x) (coord g y) := by
    rw [Real.dist_eq, Real.dist_eq, show coord g x - coord g y = (x - y) / scale g by
      unfold coord
      ring, abs_div, abs_of_pos (scale_pos g)]
    field_simp
  rw [edist_dist, edist_dist, hdist, ENNReal.ofReal_mul (scale_pos g).le]
  rw [ENNReal.ofReal_eq_coe_nnreal (scale_pos g).le]
  exact le_rfl

private theorem coord_growth (g : Affine c) : (coord g).HasTemperateGrowth := by
  unfold coord
  change (fun x : ℝ => (x + g.a) * (scale g)⁻¹).HasTemperateGrowth
  fun_prop

/-- Affine pullback acts on the Schwartz domain before passage to equivalence classes. -/
def schwartzPull (g : Affine c) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  weight g • SchwartzMap.compCLMOfAntilipschitz ℂ (coord_growth g) (coord_anti g) f

private theorem schwartzPull_apply (g : Affine c) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzPull g f x = weight g * f (coord g x) := by
  simp only [schwartzPull, smul_apply, smul_eq_mul]
  congr 1

private theorem pull_toLp (g : Affine c) (f : 𝓢(ℝ, ℂ)) :
    pull g (f.toLp 2) = (schwartzPull g f).toLp 2 := by
  apply Lp.ext
  filter_upwards [pull_ae g (f.toLp 2),
    pullAE g (p := fun x => f.toLp 2 volume x = f x) (f.coeFn_toLp 2 volume),
    (schwartzPull g f).coeFn_toLp 2] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, schwartzPull_apply]

private theorem fourier_schwartzPull (g : Affine c) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (schwartzPull g f)) ξ =
      (Real.sqrt (scale g) : ℂ) * phase g.a ξ * (𝓕 f) (scale g * ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [schwartzPull_apply, smul_eq_mul]
  let k : ℝ → ℂ := fun y => Complex.exp (↑(-2 * Real.pi * y * (scale g * ξ)) * Complex.I) * f y
  have hk : StronglyMeasurable k := by
    have hf := f.continuous
    apply Continuous.stronglyMeasurable
    fun_prop
  have hchange : (∫ x : ℝ, k (coord g x)) = (scale g : ℝ) • ∫ y : ℝ, k y := by
    rw [← integral_map_of_stronglyMeasurable (coord_measurable g) hk, affine_map_volume,
      integral_smul_measure, ENNReal.toReal_ofReal (scale_pos g).le]
  have he (x : ℝ) : Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) =
      phase g.a ξ * Complex.exp (↑(-2 * Real.pi * coord g x * (scale g * ξ)) * Complex.I) := by
    rw [phase, ← Complex.exp_add]
    congr 1
    rw [← add_mul, ← Complex.ofReal_add]
    congr 2
    have hs := (scale_pos g).ne'
    calc
      _ = g.a * frequency ξ + -2 * Real.pi * (x + g.a) * ξ := by unfold frequency; ring
      _ = _ := by
        rw [← show coord g x * scale g = x + g.a from div_mul_cancel₀ _ hs]
        ring
  calc
    _ = ∫ x : ℝ, (weight g * phase g.a ξ) * k (coord g x) := by
      congr 1
      funext x
      rw [he]
      dsimp only [k]
      ring
    _ = (weight g * phase g.a ξ) * ((scale g : ℝ) • ∫ y : ℝ, k y) := by
      rw [integral_const_mul, hchange]
    _ = _ := by
      rw [Complex.real_smul, weight_eq]
      have hs := (Real.sqrt_pos.2 (scale_pos g)).ne'
      have hsq := Real.sq_sqrt (scale_pos g).le
      have h : ((Real.sqrt (scale g))⁻¹ : ℂ) * (scale g : ℂ) = (Real.sqrt (scale g) : ℂ) := by
        exact_mod_cast (show (Real.sqrt (scale g))⁻¹ * scale g = Real.sqrt (scale g) by
          calc
            _ = (Real.sqrt (scale g))⁻¹ * (Real.sqrt (scale g)) ^ 2 :=
              congrArg ((Real.sqrt (scale g))⁻¹ * ·) hsq.symm
            _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hs, one_mul])
      change _ = _ * _ * ∫ y : ℝ, k y
      calc
        _ = (((Real.sqrt (scale g))⁻¹ : ℂ) * (scale g : ℂ)) * phase g.a ξ *
            ∫ y : ℝ, k y := by push_cast; ring
        _ = _ := by rw [h]

private theorem memLp_phase (a : ℝ) (f : PositionL2) :
    MemLp (fun ξ => phase a ξ * f ξ) 2 volume := by
  have hp : Continuous (phase a) := by
    unfold phase frequency
    fun_prop
  apply (Lp.memLp f).congr_norm (hp.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖f ξ‖ = ‖phase a ξ * f ξ‖
    rw [norm_mul, phase_norm, one_mul]

private def phasePull (a : ℝ) (f : PositionL2) : PositionL2 :=
  (memLp_phase a f).toLp _

private theorem phasePull_ae (a : ℝ) (f : PositionL2) :
    ⇑(phasePull a f) =ᵐ[volume] fun ξ => phase a ξ * f ξ :=
  (memLp_phase a f).coeFn_toLp

private def phaseLinear (a : ℝ) : PositionL2 →ₗᵢ[ℂ] PositionL2 where
  toFun := phasePull a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [phasePull_ae a (f + g), phasePull_ae a f, phasePull_ae a g,
      Lp.coeFn_add f g, Lp.coeFn_add (phasePull a f) (phasePull a g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁, h₅, h₂, h₃, h₄, mul_add]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [phasePull_ae a (z • f), phasePull_ae a f, Lp.coeFn_smul z f,
      Lp.coeFn_smul z (phasePull a f)] with x h₁ h₂ h₃ h₄
    simp only [Pi.smul_apply, smul_eq_mul] at h₃ h₄
    rw [RingHom.id_apply, h₁, h₄, h₂, h₃]
    ring
  norm_map' f := by
    change ‖(memLp_phase a f).toLp (fun ξ => phase a ξ * f ξ)‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (memLp_phase a f).aestronglyMeasurable (Lp.aestronglyMeasurable f)
    exact Filter.Eventually.of_forall fun ξ => by rw [norm_mul, phase_norm, one_mul]

private def freqDilation (g : Affine c) : Affine c := dilation c (-g.s)

private theorem freqDilation_coord (g : Affine c) (ξ : ℝ) :
    coord (freqDilation g) ξ = scale g * ξ := by
  simp [coord, freqDilation, dilation, scale, mul_neg, Real.exp_neg, div_eq_inv_mul]

private theorem freqDilation_weight (g : Affine c) :
    weight (freqDilation g) = (Real.sqrt (scale g) : ℂ) := by
  rw [sqrt_scale]
  unfold weight freqDilation dilation
  push_cast
  congr 2
  ring

private def freqPull (g : Affine c) (f : PositionL2) : PositionL2 :=
  phasePull g.a (pull (freqDilation g) f)

private theorem freqPull_ae (g : Affine c) (f : PositionL2) :
    ⇑(freqPull g f) =ᵐ[volume]
      fun ξ => (Real.sqrt (scale g) : ℂ) * phase g.a ξ * f (scale g * ξ) := by
  filter_upwards [phasePull_ae g.a (pull (freqDilation g) f), pull_ae (freqDilation g) f]
    with ξ h₁ h₂
  change (phasePull g.a (pull (freqDilation g) f)) ξ = _
  rw [h₁, h₂, freqDilation_weight, freqDilation_coord]
  ring

private theorem fourier_pull (g : Affine c) (f : PositionL2) :
    𝓕 (pull g f) = freqPull g (𝓕 f) := by
  apply DenseRange.induction_on (p := fun f : PositionL2 => 𝓕 (pull g f) = freqPull g (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (pullLinear g).continuous
    · exact (phaseLinear g.a).continuous.comp ((pullLinear (freqDilation g)).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  intro f
  change 𝓕 (pull g (f.toLp 2)) = freqPull g (𝓕 (f.toLp 2))
  rw [pull_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzPull g f)).coeFn_toLp 2 volume,
    freqPull_ae g ((𝓕 f).toLp 2),
    pullAE (freqDilation g)
      (p := fun x => (𝓕 f).toLp 2 volume x = (𝓕 f) x) ((𝓕 f).coeFn_toLp 2 volume)]
    with ξ h₁ h₂ h₃
  rw [freqDilation_coord] at h₃
  rw [h₁, h₂, h₃, fourier_schwartzPull]

/-- Plancherel transports the unitary action to a phase and reciprocal dilation. -/
theorem fourier_affineUnitary_ae (g : Affine c) (f : PositionL2) :
    ⇑(𝓕 (affineUnitary c g f) : PositionL2) =ᵐ[volume]
      fun ξ => (Real.sqrt (scale g) : ℂ) * phase g.a ξ * (𝓕 f : PositionL2) (scale g * ξ) := by
  change ⇑(𝓕 (pullEquiv g f) : PositionL2) =ᵐ[volume] _
  rw [show pullEquiv g f = pull g f by simp [pullEquiv, pullLinear], fourier_pull]
  exact freqPull_ae g (𝓕 f)

/-- Fourier-conjugated affine action preserves almost-everywhere nonnegative frequency support. -/
theorem hardyInvariant (g : Affine c) (f : PositionL2)
    (hf : ∀ᵐ ξ ∂volume, ξ < 0 → (𝓕 f : PositionL2) ξ = 0) :
    ∀ᵐ ξ ∂volume, ξ < 0 → (𝓕 (affineUnitary c g f) : PositionL2) ξ = 0 := by
  filter_upwards [fourier_affineUnitary_ae g f, pullAE (freqDilation g) hf] with ξ h₁ h₂ hξ
  rw [freqDilation_coord] at h₂
  rw [h₁, h₂ (mul_neg_of_pos_of_neg (scale_pos g) hξ), mul_zero]

/-- The derivatives of the Fourier phases determine the translation multiplier. -/
theorem phase_hasDerivAt (a ξ : ℝ) :
    HasDerivAt (fun t => phase t ξ) (phase a ξ * ((frequency ξ : ℂ) * Complex.I)) a := by
  have he : HasDerivAt (fun t : ℝ => ((t * frequency ξ : ℝ) : ℂ) * Complex.I)
      ((frequency ξ : ℂ) * Complex.I) a := by
    simpa using ((hasDerivAt_id a).mul_const (frequency ξ)).ofReal_comp.mul_const Complex.I
  exact (Complex.hasDerivAt_exp _).comp a he

/-- Differentiation of translation on the Fourier representative of a Schwartz vector. -/
theorem schwartz_translation_deriv (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    HasDerivAt (fun a => phase a ξ * f ξ) (Complex.I * schwartzP f ξ) 0 := by
  convert (phase_hasDerivAt 0 ξ).mul_const (f ξ) using 1
  rw [schwartzP_apply]
  simp [phase]
  ring

/-- Differentiation of dilation on the Fourier representative of a Schwartz vector. -/
theorem schwartz_dilation_deriv (c : ℝ) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    HasDerivAt (fun s => (Real.sqrt (scale (dilation c s)) : ℂ) *
      f (scale (dilation c s) * ξ)) (-Complex.I * schwartzK c f ξ) 0 := by
  have hw : HasDerivAt (fun s : ℝ => (Real.exp (c * s / 2) : ℂ)) (↑(c / 2) : ℂ) 0 := by
    simpa using (Real.hasDerivAt_exp _ |>.comp 0 (((hasDerivAt_id 0).const_mul c).div_const 2)
      |>.ofReal_comp)
  have harg : HasDerivAt (fun s : ℝ => Real.exp (c * s) * ξ) (c * ξ) 0 := by
    simpa using ((Real.hasDerivAt_exp _).comp 0 ((hasDerivAt_id 0).const_mul c)).mul_const ξ
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp (c * s) * ξ))
      ((c * ξ) • deriv f ξ) 0 := by
    simpa [Function.comp_def] using
      (f.differentiableAt (x := Real.exp (c * 0) * ξ)).hasDerivAt.scomp 0 harg
  simp_rw [sqrt_scale, scale, dilation]
  convert hw.mul hcomp using 1
  rw [schwartzK_apply]
  simp only [mul_zero, zero_div, Real.exp_zero, Complex.ofReal_one, one_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hi : -Complex.I * (Complex.I * (c : ℂ)) = (c : ℂ) := by
    rw [← mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, one_mul]
  rw [← mul_assoc, hi]
  ring

end Omega.RealAffine
