/- GID: D5/S3/Fourier/CenterFiberMomentRepresentation
   generality: G
   mirror-B: D5/B/S3/Fourier/CenterFiberMomentRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Even difference moments admit a nonnegative center-fiber Fourier density. -/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/- Library-search audit trail (2026-09-03):
   * Six-way repository search found Fourier representations and moment kernels,
     but no center--fiber moment formula; no in-flight lane owns this GID or atom.
     The full `Weil/TestFunctions` bucket was avoided in favor of the registered
     `Fourier` domain.
   * Pinned Mathlib has no packaged statement of this formula. The proof directly
     uses `Measure.map_linearMap_addHaar_eq_smul_addHaar`, the determinant
     formula for a two-by-two matrix, `MeasureTheory.integral_map`, and Fubini's
     theorem `MeasureTheory.integral_prod`.
   * The source omits hypotheses needed for its integrals and for `C_m ≥ 0`.
     We require a continuous nonnegative real kernel and absolute integrability
     of the center--fiber moment kernel. -/

noncomputable section

open MeasureTheory
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CenterFiberMomentRepresentation

private def centerFiberMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(1 : ℝ), 1; 1, -1]

@[simp]
private theorem centerFiberMap_apply (p : ℝ × ℝ) :
    centerFiberMap p = (p.1 + p.2, p.1 - p.2) := by
  simp [centerFiberMap, sub_eq_add_neg]

private theorem centerFiberMap_det : LinearMap.det centerFiberMap = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  norm_num [centerFiberMap, Matrix.det_fin_two]

/-- The inverse Jacobian of `(x,y) ↦ (x+y,x-y)` is `1/2`. -/
private theorem half_integral_centerFiberMap
    (F : ℝ × ℝ → ℂ) (hF : StronglyMeasurable F) :
    (1 / 2 : ℂ) * ∫ q : ℝ × ℝ, F q =
      ∫ p : ℝ × ℝ, F (centerFiberMap p) := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hdet : LinearMap.det centerFiberMap ≠ 0 := by
    rw [centerFiberMap_det]
    norm_num
  have hmap :
      Measure.map centerFiberMap (volume : Measure (ℝ × ℝ)) =
        ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (ℝ × ℝ)) hdet, centerFiberMap_det]
    norm_num
  calc
    (1 / 2 : ℂ) * ∫ q : ℝ × ℝ, F q =
        ∫ q : ℝ × ℝ, F q ∂(ENNReal.ofReal (1 / 2 : ℝ) • volume) := by
          rw [integral_smul_measure]
          norm_num
    _ = ∫ q : ℝ × ℝ, F q ∂Measure.map centerFiberMap volume := by rw [hmap]
    _ = ∫ p : ℝ × ℝ, F (centerFiberMap p) :=
      integral_map_of_stronglyMeasurable
        centerFiberMap.continuous_of_finiteDimensional.measurable hF

/-- The nonnegative density obtained by integrating the even moment along the
fiber `v = x-y` at fixed center coordinate `u = x+y`. -/
def centerFiberMomentDensity (φ : ℝ → ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (1 / (2 * ((2 * m).factorial : ℝ))) *
    ∫ v : ℝ,
      v ^ (2 * m) * φ ((u + v) / 2) * φ ((u - v) / 2)

/-- Under the missing positivity and absolute-integrability hypotheses, the
even difference moment is the Fourier transform of the nonnegative
center--fiber density. The proof performs the linear coordinate change and
accounts for its Jacobian rather than assuming the representation. -/
theorem center_fiber_moment_representation
    (φ : ℝ → ℝ) (m : ℕ) (t : ℝ)
    (hφ : Continuous φ) (hφ_nonnegative : ∀ x, 0 ≤ φ x)
    (hcore : Integrable (fun q : ℝ × ℝ =>
      q.2 ^ (2 * m) * φ ((q.1 + q.2) / 2) * φ ((q.1 - q.2) / 2))) :
    let J : ℂ :=
      (1 / ((2 * m).factorial : ℂ)) *
        ∫ p : ℝ × ℝ,
          ((φ p.1 * φ p.2 * (p.1 - p.2) ^ (2 * m) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (t * (p.1 + p.2) : ℝ))
    let C : ℝ → ℝ := centerFiberMomentDensity φ m
    J = ∫ u : ℝ, (C u : ℂ) * Complex.exp (Complex.I * (t * u : ℝ)) ∧
      ∀ u : ℝ, 0 ≤ C u := by
  dsimp only
  let core : ℝ × ℝ → ℝ := fun q =>
    q.2 ^ (2 * m) * φ ((q.1 + q.2) / 2) * φ ((q.1 - q.2) / 2)
  let phase : ℝ × ℝ → ℂ := fun q =>
    Complex.exp (Complex.I * (t * q.1 : ℝ))
  let F : ℝ × ℝ → ℂ := fun q => (core q : ℂ) * phase q
  have hcore_continuous : Continuous core := by
    dsimp only [core]
    fun_prop
  have hphase_continuous : Continuous phase := by
    dsimp only [phase]
    fun_prop
  have hF_continuous : Continuous F := by
    dsimp only [F]
    fun_prop
  have hF_integrable : Integrable F := by
    apply hcore.ofReal.mul_bdd (c := 1)
    · exact hphase_continuous.aestronglyMeasurable
    · filter_upwards with q
      simp [phase, Complex.norm_exp]
  have hinner (u : ℝ) :
      (centerFiberMomentDensity φ m u : ℂ) *
          Complex.exp (Complex.I * (t * u : ℝ)) =
        (1 / (2 * ((2 * m).factorial : ℂ))) *
          ∫ v : ℝ, F (u, v) := by
    simp only [centerFiberMomentDensity, F, core, phase, integral_mul_const,
      integral_complex_ofReal]
    push_cast
    ring
  constructor
  · calc
      (1 / ((2 * m).factorial : ℂ)) *
          ∫ p : ℝ × ℝ,
            ((φ p.1 * φ p.2 * (p.1 - p.2) ^ (2 * m) : ℝ) : ℂ) *
              Complex.exp (Complex.I * (t * (p.1 + p.2) : ℝ)) =
          (1 / ((2 * m).factorial : ℂ)) *
            ∫ p : ℝ × ℝ, F (centerFiberMap p) := by
              congr 1
              apply integral_congr_ae
              filter_upwards with p
              simp only [F, core, phase, centerFiberMap_apply]
              have hx : ((p.1 + p.2) + (p.1 - p.2)) / 2 = p.1 := by ring
              have hy : ((p.1 + p.2) - (p.1 - p.2)) / 2 = p.2 := by ring
              rw [hx, hy]
              push_cast
              ring
      _ = (1 / (2 * ((2 * m).factorial : ℂ))) *
            ∫ q : ℝ × ℝ, F q := by
              rw [← half_integral_centerFiberMap F hF_continuous.stronglyMeasurable]
              ring
      _ = (1 / (2 * ((2 * m).factorial : ℂ))) *
            ∫ u : ℝ, ∫ v : ℝ, F (u, v) := by
              have hfubini := integral_prod F hF_integrable
              simpa only [Measure.volume_eq_prod] using congrArg
                (fun z => (1 / (2 * ((2 * m).factorial : ℂ))) * z) hfubini
      _ = ∫ u : ℝ,
            (centerFiberMomentDensity φ m u : ℂ) *
              Complex.exp (Complex.I * (t * u : ℝ)) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with u
              exact hinner u |>.symm
  · intro u
    apply mul_nonneg
    · have hfactorial : (0 : ℝ) < ((2 * m).factorial : ℝ) := by positivity
      positivity
    · apply integral_nonneg
      intro v
      exact mul_nonneg
        (mul_nonneg ((even_two_mul m).pow_nonneg v)
          (hφ_nonnegative ((u + v) / 2)))
        (hφ_nonnegative ((u - v) / 2))

#print axioms center_fiber_moment_representation

end D5.S3.Fourier.CenterFiberMomentRepresentation
