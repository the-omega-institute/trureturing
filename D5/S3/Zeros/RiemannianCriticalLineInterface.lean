/- GID: D5/S3/Zeros/RiemannianCriticalLineInterface
   generality: I
   mirror-B: D5/B/S3/Zeros/RiemannianCriticalLineInterface
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Encode the critical-line condition as a fixed-point and zero-displacement
   condition in the hyperbolic upper-half-space metric. -/

import D5.S3.Geometry.HyperbolicUpperHalfSpace
import D5.S3.Zeros.ActualZeroGeometry
import D5.S3.Zeros.Symmetry.CriticalCenterCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.RiemannianCriticalLineInterface

open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Weil.Convention
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Zeros.Symmetry.CriticalCenterCoordinate

/-- The canonical base point in the real hyperbolic upper-half-space model. -/
def basepoint : HyperbolicSpace ℝ :=
  ⟨⟨WithLp.toLp 2 ((0 : ℝ), (1 : ℝ)), by norm_num⟩⟩

/-- The signed normal offset from the critical line. -/
def normalOffset (rho : ℂ) : ℝ := rho.re - criticalAbscissa

/-- A normal offset acts on the hyperbolic model by horizontal translation. -/
def normalTranslation (rho : ℂ) : HyperbolicSpace ℝ ≃ᵢ HyperbolicSpace ℝ :=
  horizontalTranslation (normalOffset rho)

/-- The displacement of the translated base point in the hyperbolic metric. -/
def normalDisplacement (rho : ℂ) : ℝ :=
  dist (normalTranslation rho basepoint) basepoint

@[simp]
theorem normal_offset_eq_neg_central_coord_im (rho : ℂ) :
    normalOffset rho = -(centralCoord rho).im := by
  simp [normalOffset, central_coord_im, criticalAbscissa]

theorem normal_translation_fixed_iff (rho : ℂ) :
    normalTranslation rho basepoint = basepoint ↔
      rho.re = criticalAbscissa := by
  rw [normalTranslation, horizontalTranslation_fixed_iff_zero]
  exact sub_eq_zero

theorem normal_displacement_eq_zero_iff (rho : ℂ) :
    normalDisplacement rho = 0 ↔ rho.re = criticalAbscissa := by
  rw [normalDisplacement, dist_eq_zero]
  exact normal_translation_fixed_iff rho

/-- The hyperbolic normal displacement is the arsinh transform of the signed offset. -/
theorem normal_displacement_eq_arsinh (rho : ℂ) :
    normalDisplacement rho = 2 * Real.arsinh (|normalOffset rho| / 2) := by
  rw [normalDisplacement, normalTranslation]
  change hyperbolicDist _ _ = _
  rw [hyperbolicDist]
  congr 1
  simp [horizontalTranslation, horizontalTranslate, basepoint, height,
    WithLp.prod_dist_eq_of_L2]
  exact Real.sqrt_sq_eq_abs _

/-- A nontrivial zero lies on the critical line exactly when its normal
translation has zero hyperbolic displacement. This is an interface theorem;
it does not assert that all zeros have zero displacement. -/
theorem nontrivial_zero_on_line_iff_normal_displacement_zero
    (rho : ℂ) (_hzero : Zeta23.IsNontrivialZero rho) :
    rho.re = criticalAbscissa ↔ normalDisplacement rho = 0 := by
  exact (normal_displacement_eq_zero_iff rho).symm

/-- The Riemann hypothesis is equivalent to vanishing of every geometric
normal displacement in the hyperbolic model. -/
theorem rh_iff_all_normal_displacements_zero :
    RiemannHypothesis ↔
      ∀ rho : ℂ, Zeta23.IsNontrivialZero rho → normalDisplacement rho = 0 := by
  rw [rh_iff_nontrivial_zeros_on_line]
  constructor
  · intro h rho hzero
    exact (normal_displacement_eq_zero_iff rho).2 (h rho hzero)
  · intro h rho hzero
    exact (normal_displacement_eq_zero_iff rho).1 (h rho hzero)

/-- The same statement in fixed-point form for the horizontal isometry. -/
theorem rh_iff_all_normal_translations_fix_basepoint :
    RiemannHypothesis ↔
      ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
        normalTranslation rho basepoint = basepoint := by
  rw [rh_iff_nontrivial_zeros_on_line]
  constructor
  · intro h rho hzero
    exact (normal_translation_fixed_iff rho).2 (h rho hzero)
  · intro h rho hzero
    exact (normal_translation_fixed_iff rho).1 (h rho hzero)

#print axioms normal_offset_eq_neg_central_coord_im
#print axioms normal_translation_fixed_iff
#print axioms normal_displacement_eq_zero_iff
#print axioms normal_displacement_eq_arsinh
#print axioms rh_iff_all_normal_displacements_zero
#print axioms rh_iff_all_normal_translations_fix_basepoint

end D5.S3.Zeros.RiemannianCriticalLineInterface
