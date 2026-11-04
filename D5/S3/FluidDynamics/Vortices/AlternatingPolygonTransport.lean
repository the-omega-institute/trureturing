/- GID: D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Vortices/AlternatingPolygonTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive physical scaling of the actual vortex derivative and every generalized eigenspace. -/

import D5.S3.FluidDynamics.Vortices.AlternatingPolygonDerivative
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonNeutral
import D5.S3.FluidDynamics.Vortices.AlternatingPolygonRealSpaces
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! Physical scaling follows from the field, and preserves every Jordan filtration. -/
noncomputable section
open scoped BigOperators
open Matrix Polynomial

namespace D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
open AlternatingPolygonSpectrum AlternatingPolygonModes AlternatingPolygonJordan
open AlternatingPolygonNeutral AlternatingPolygonDecomposition AlternatingPolygonRealSpaces

/-- Scalar dilation preserves every level of the generalized-eigenspace filtration. -/
theorem smul_genEigenspace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) {a : K} (ha : a ≠ 0) (μ : K) (n : ℕ∞) :
    (a • A).genEigenspace (a * μ) n = A.genEigenspace μ n := by
  have hshift : a • A - (a * μ) • (1 : Module.End K V) = a • (A - μ • 1) := by
    rw [smul_sub, smul_smul]
  ext v
  simp only [Module.End.mem_genEigenspace]
  have hp (k : ℕ) : ((a • A - (a * μ) • (1 : Module.End K V)) ^ k) v =
      a ^ k • ((A - μ • 1) ^ k) v := by
    rw [hshift, smul_pow]
    rfl
  simp only [LinearMap.mem_ker, hp, smul_eq_zero, pow_ne_zero _ ha, false_or]

/-- Determinant scaling, including the zero characteristic root. -/
theorem charpoly_smul_eval {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) {a : K} (ha : a ≠ 0) (x : K) :
    (a • A).charpoly.eval x = a ^ Fintype.card ι * A.charpoly.eval (x / a) := by
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly, ← Matrix.det_smul]
  congr 1
  rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← smul_smul,
    smul_eq_mul, mul_div_cancel₀ _ ha]

/-- Polynomial, rather than root-list, scaling of an actual square matrix. -/
theorem charpoly_smul_polynomial {K ι : Type*} [Field K] [Infinite K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) {a : K} (ha : a ≠ 0) :
    (a • A).charpoly = C (a ^ Fintype.card ι) * A.charpoly.comp (C a⁻¹ * X) := by
  apply Polynomial.funext
  intro x
  rw [charpoly_smul_eval A ha]
  simp [Polynomial.eval_comp, div_eq_mul_inv, mul_comm]

/-- The physical derivative at the radius selected by b and Omega. -/
def parameterOperator (m : ℕ) (b Ω : ℝ) : Module.End ℂ (Cartesian m) :=
  ((AlternatingPolygonParameters.jacobian (2 * m) b Ω
    (AlternatingPolygonParameters.radius b Ω • polygon (2 * m))).map Complex.ofRealHom).toLin'

theorem parameterOperator_eq (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    parameterOperator m b Ω = (2 * Ω : ℂ) • actualOperator m := by
  have hR := ne_of_gt (AlternatingPolygonParameters.radius_pos hb hΩ)
  have hbR : b = 4 * Ω * AlternatingPolygonParameters.radius b Ω ^ 2 := by
    rw [AlternatingPolygonParameters.radius_sq hb hΩ]
    field_simp
  unfold parameterOperator actualOperator
  rw [AlternatingPolygonParameters.jacobian_scaling _ hR hbR]
  apply LinearMap.ext
  intro v
  ext p
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  push_cast
  ring

/-- Every eigenvalue and every Jordan filtration level transports from the actual field. -/
theorem parameter_genEigenspace (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω)
    (μ : ℂ) (n : ℕ∞) :
    (parameterOperator m b Ω).genEigenspace ((2 * Ω : ℂ) * μ) n =
      (actualOperator m).genEigenspace μ n := by
  rw [parameterOperator_eq m hb hΩ]
  exact smul_genEigenspace _ (Complex.ofReal_ne_zero.mpr (by positivity)) μ n

theorem parameter_charpoly (m : ℕ) {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    ((AlternatingPolygonParameters.jacobian (2 * m) b Ω
      (AlternatingPolygonParameters.radius b Ω • polygon (2 * m))).map Complex.ofRealHom).charpoly =
      C ((2 * Ω : ℂ) ^ (4 * m)) *
        (((jacobian (2 * m)).map Complex.ofRealHom).charpoly).comp
          (C (2 * Ω : ℂ)⁻¹ * X) := by
  have h := congrArg LinearMap.charpoly (parameterOperator_eq m hb hΩ)
  simp only [parameterOperator, actualOperator, Matrix.charpoly_toLin',
    ← Matrix.toLin'_smul] at h
  rw [h, charpoly_smul_polynomial _ (Complex.ofReal_ne_zero.mpr (by positivity))]
  simp [Fintype.card_sum, show 2 * m + 2 * m = 4 * m by omega]

/-- The chain length stays two; only the generalized vector is rescaled. -/
theorem parameter_neutral_chain (m : ℕ) [NeZero (2 * m)] (hm : 1 ≤ m)
    {b Ω : ℝ} (hb : 0 < b) (hΩ : 0 < Ω) :
    parameterOperator m b Ω (neutral0 m) = 0 ∧
      parameterOperator m b Ω ((2 * Ω : ℂ)⁻¹ • neutral1 m) = neutral0 m := by
  have ha : (2 * Ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [parameterOperator_eq m hb hΩ]
  constructor
  · simp only [LinearMap.smul_apply, (neutral_chain m hm).1, smul_zero]
  · rw [LinearMap.smul_apply, map_smul, (neutral_chain m hm).2, smul_smul,
      mul_inv_cancel₀ ha, one_smul]

end D5.S3.FluidDynamics.Vortices.AlternatingPolygonTransport
