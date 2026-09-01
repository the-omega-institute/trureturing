/- GID: D5/S3/Analytic/Adelic/EllipticHyperbolicReflectionTrichotomy
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/EllipticHyperbolicReflectionTrichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-dimensional generators separate hyperbolic, neutral, and elliptic spectral sectors by determinant sign. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `EllipticHyperbolicReflectionTrichotomy`,
     `rotationGenerator`, `ellipticGenerator`, and the determinant-sign package
     found only research targets and unrelated matrix owners.
   * The frozen `ReflectedGrowthPairNegativeSquare` owner supplies the scalar
     hyperbolic signed determinant `-delta^2`. This module identifies it with
     the determinant of the real diagonal generator rather than introducing a
     second negative-square definition.
   * Pinned Mathlib supplies matrix notation, `Matrix.det_fin_two`,
     `Matrix.trace_fin_two`, and finite two-coordinate sums. The concrete
     determinant and square calculations below use those declarations.
   * The classification is finite-dimensional and algebraic. It does not claim
     that completed zeta has already been realized by either generator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix

namespace D5.S3.Analytic.Adelic.EllipticHyperbolicReflectionTrichotomy

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare

/-- A real two-dimensional carrier for the three spectral sectors. -/
abbrev PlaneGenerator := Matrix (Fin 2) (Fin 2) ℝ

/-- The growth-decay generator with reflected rates `delta` and `-delta`. -/
def hyperbolicGenerator (delta : ℝ) : PlaneGenerator :=
  !![delta, 0; 0, -delta]

/-- The real rotation generator with angular rate `gamma`. -/
def ellipticGenerator (gamma : ℝ) : PlaneGenerator :=
  !![0, -gamma; gamma, 0]

/-- The unsplit neutral generator. -/
def neutralGenerator : PlaneGenerator :=
  0

/-- The hyperbolic generator has zero trace and negative-square determinant. -/
theorem hyperbolic_generator_trace_det (delta : ℝ) :
    Matrix.trace (hyperbolicGenerator delta) = 0 ∧
      Matrix.det (hyperbolicGenerator delta) = -(delta ^ 2) := by
  constructor
  · simp [hyperbolicGenerator, Matrix.trace_fin_two]
  · simp [hyperbolicGenerator, Matrix.det_fin_two]
    ring

/-- The determinant of the real hyperbolic generator is exactly the frozen
reflected-pair signed determinant. -/
theorem hyperbolic_det_eq_reflection_pair_signed_determinant (delta : ℝ) :
    Matrix.det (hyperbolicGenerator delta) =
      reflectionPairSignedDeterminant delta := by
  rw [(hyperbolic_generator_trace_det delta).2,
    (reflection_pair_signed_determinant delta 0).2.1]

/-- Squaring the hyperbolic generator produces positive scalar expansion. -/
theorem hyperbolic_generator_square (delta : ℝ) :
    hyperbolicGenerator delta * hyperbolicGenerator delta =
      !![delta ^ 2, 0; 0, delta ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicGenerator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The elliptic rotation generator has zero trace and positive-square determinant. -/
theorem elliptic_generator_trace_det (gamma : ℝ) :
    Matrix.trace (ellipticGenerator gamma) = 0 ∧
      Matrix.det (ellipticGenerator gamma) = gamma ^ 2 := by
  constructor
  · simp [ellipticGenerator, Matrix.trace_fin_two]
  · simp [ellipticGenerator, Matrix.det_fin_two]
    ring

/-- Squaring the elliptic generator produces negative scalar curvature. -/
theorem elliptic_generator_square (gamma : ℝ) :
    ellipticGenerator gamma * ellipticGenerator gamma =
      !![-(gamma ^ 2), 0; 0, -(gamma ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticGenerator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The neutral generator has zero trace, zero determinant, and zero square. -/
theorem neutral_generator_trace_det_square :
    Matrix.trace neutralGenerator = 0 ∧
      Matrix.det neutralGenerator = 0 ∧
      neutralGenerator * neutralGenerator = 0 := by
  simp [neutralGenerator]

/-- Every nonzero reflected split has strictly negative determinant. -/
theorem hyperbolic_generator_det_neg_of_ne_zero
    (delta : ℝ) (hdelta : delta ≠ 0) :
    Matrix.det (hyperbolicGenerator delta) < 0 := by
  rw [(hyperbolic_generator_trace_det delta).2]
  negativity

/-- Every nonzero angular rate has strictly positive determinant. -/
theorem elliptic_generator_det_pos_of_ne_zero
    (gamma : ℝ) (hgamma : gamma ≠ 0) :
    0 < Matrix.det (ellipticGenerator gamma) := by
  rw [(elliptic_generator_trace_det gamma).2]
  positivity

/-- The exact finite trichotomy: negative determinant and positive square for
hyperbolic growth-decay, zero determinant for the neutral mode, and positive
determinant with negative square for elliptic rotation. -/
theorem elliptic_hyperbolic_reflection_trichotomy
    (delta gamma : ℝ) :
    (Matrix.trace (hyperbolicGenerator delta) = 0 ∧
      Matrix.det (hyperbolicGenerator delta) = -(delta ^ 2) ∧
      hyperbolicGenerator delta * hyperbolicGenerator delta =
        !![delta ^ 2, 0; 0, delta ^ 2]) ∧
    (Matrix.trace neutralGenerator = 0 ∧
      Matrix.det neutralGenerator = 0 ∧
      neutralGenerator * neutralGenerator = 0) ∧
    (Matrix.trace (ellipticGenerator gamma) = 0 ∧
      Matrix.det (ellipticGenerator gamma) = gamma ^ 2 ∧
      ellipticGenerator gamma * ellipticGenerator gamma =
        !![-(gamma ^ 2), 0; 0, -(gamma ^ 2)]) := by
  exact ⟨⟨(hyperbolic_generator_trace_det delta).1,
      (hyperbolic_generator_trace_det delta).2,
      hyperbolic_generator_square delta⟩,
    neutral_generator_trace_det_square,
    ⟨(elliptic_generator_trace_det gamma).1,
      (elliptic_generator_trace_det gamma).2,
      elliptic_generator_square gamma⟩⟩

/-- The sign hypotheses in the nondegenerate sectors are inhabited. -/
example :
    Matrix.det (hyperbolicGenerator 1) < 0 ∧
      0 < Matrix.det (ellipticGenerator 1) := by
  exact ⟨hyperbolic_generator_det_neg_of_ne_zero 1 one_ne_zero,
    elliptic_generator_det_pos_of_ne_zero 1 one_ne_zero⟩

#print axioms hyperbolic_det_eq_reflection_pair_signed_determinant
#print axioms elliptic_hyperbolic_reflection_trichotomy
#print axioms hyperbolic_generator_det_neg_of_ne_zero
#print axioms elliptic_generator_det_pos_of_ne_zero

end D5.S3.Analytic.Adelic.EllipticHyperbolicReflectionTrichotomy
