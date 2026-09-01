/- GID: D5/S3/Observer/GoldenCoding/GoldenHyperbolicAxis
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenHyperbolicAxis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden Mobius map has exactly two fixed endpoints and an explicit axis length. -/

import D5.S0.Tower.QuadraticFixedPoint
import D5.S1.Eigenstructure.FibonacciMatrixDiscriminant
import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open with empty `coverage_gids`, no coverage
     receipt, and no formalization receipt. Its four chain atoms are likewise
     residual-open with no coverage GID.
   * Repository searches for the affine map, both golden fixed points,
     quadratic fixed-point characterizations, Fibonacci determinants,
     hyperbolic axes, and golden logarithmic periods found exact reusable
     subresults but no theorem packaging the atom's complete conclusion.
   * `quadratic_fixed_point_iff`, `golden_mobius_fixed_golden`,
     `golden_mobius_fixed_conjugate`,
     `fibonacci_substitution_trace_det_discriminant`, `goldenScalePeriod`, and
     `abs_golden_projective_multiplier` are imported and applied below.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, `Real.goldenConj_sq`, their
     sum, product, inverse, sign and nonzero identities, `Matrix.det_fin_two`,
     `Real.arcosh_cosh`, and exponential-log identities. It has no exact
     all-real two-root classification or complete axis package.
   * A NyxID-proxied GitHub ecosystem search was attempted. The discovered
     `api-github` service returned `Bad request: API key is failed`, and the
     discovered `api-github-pat` slug returned `Service not found`; therefore
     third-party search completion is not claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped goldenRatio Matrix

namespace D5.S3.Observer.GoldenCoding.GoldenHyperbolicAxis

open D5.S0.Tower.QuadraticFixedPoint
open D5.S1.Eigenstructure.FibonacciMatrixDiscriminant
open D5.S1.Scale
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative
open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix

/-- The Euclidean circle underlying the golden geodesic in the upper half-plane model. -/
def goldenAxisCircle (x y : Real) : Prop :=
  (x - 1 / 2) ^ 2 + y ^ 2 = 5 / 4

/-- The trace formula for the translation length of the squared Fibonacci matrix. -/
def goldenAxisTranslationLength : Real :=
  2 * Real.arcosh (3 / 2)

/-- The observer index singled out by the orientation-preserving golden step. -/
def goldenObserverIndex : Real :=
  Real.goldenRatio ^ 2

/-- The positive projection weight attached to the golden projective multiplier. -/
def goldenProjectionWeight : Real :=
  (Real.goldenRatio⁻¹) ^ 2

/-- The complete elementary golden-axis package: the affine fixed-point
classification, matrix square, circle endpoints, trace length, observer index,
and projection weight. The affine iterate carries the two denominator
hypotheses that are implicit in the corresponding projective formula. -/
theorem golden_hyperbolic_axis :
    (∀ z : Real, z ≠ 0 →
      (goldenMobius z = z ↔ z ^ 2 = z + 1)) ∧
    (∀ z : Real, z ^ 2 = z + 1 ↔
      z = Real.goldenRatio ∨ z = Real.goldenConj) ∧
    (∀ z : Real, goldenMobius z = z ↔
      z = Real.goldenRatio ∨ z = Real.goldenConj) ∧
    (Real.goldenConj = 1 - Real.goldenRatio ∧
      Real.goldenConj = -(Real.goldenRatio⁻¹)) ∧
    (Real.goldenRatio ≠ 0 ∧ Real.goldenConj ≠ 0) ∧
    (goldenMobius Real.goldenRatio = Real.goldenRatio ∧
      goldenMobius Real.goldenConj = Real.goldenConj) ∧
    (goldenMobius 1 = 2 ∧ goldenMobius 1 ≠ 1) ∧
    (∀ z : Real, z ≠ 0 → z ≠ -1 →
      goldenMobius (goldenMobius z) = (2 * z + 1) / (z + 1)) ∧
    fibonacciSubstitution ^ 2 = !![2, 1; 1, 1] ∧
    (Matrix.det fibonacciSubstitution = -1 ∧
      Matrix.det (fibonacciSubstitution ^ 2) = 1 ∧
      Matrix.trace (fibonacciSubstitution ^ 2) = 3) ∧
    (goldenAxisCircle Real.goldenRatio 0 ∧
      goldenAxisCircle Real.goldenConj 0 ∧
      goldenAxisCircle (1 / 2) (Real.sqrt 5 / 2) ∧
      0 < Real.sqrt 5 / 2) ∧
    goldenObserverIndex = Real.goldenRatio ^ 2 ∧
    goldenProjectionWeight = (Real.goldenRatio⁻¹) ^ 2 ∧
    goldenAxisTranslationLength = 4 * Real.log Real.goldenRatio ∧
    goldenAxisTranslationLength / 2 = goldenScalePeriod ∧
    goldenScalePeriod = Real.log goldenObserverIndex ∧
    Real.exp (-goldenAxisTranslationLength / 2) = goldenProjectionWeight ∧
    |goldenProjectiveMultiplier| = goldenProjectionWeight := by
  have hFixedQuadratic : ∀ z : Real, z ≠ 0 →
      (goldenMobius z = z ↔ z ^ 2 = z + 1) := by
    intro z hz
    constructor
    · intro hFixed
      exact (quadratic_fixed_point_iff z hz).2 hFixed.symm
    · intro hQuadratic
      exact ((quadratic_fixed_point_iff z hz).1 hQuadratic).symm
  have hRoots : ∀ z : Real, z ^ 2 = z + 1 ↔
      z = Real.goldenRatio ∨ z = Real.goldenConj := by
    intro z
    constructor
    · intro hQuadratic
      have hFactor :
          (z - Real.goldenRatio) * (z - Real.goldenConj) = 0 := by
        calc
          (z - Real.goldenRatio) * (z - Real.goldenConj) =
              z ^ 2 - z * (Real.goldenRatio + Real.goldenConj) +
                Real.goldenRatio * Real.goldenConj := by ring
          _ = 0 := by
            rw [Real.goldenRatio_add_goldenConj,
              Real.goldenRatio_mul_goldenConj]
            nlinarith
      rcases mul_eq_zero.mp hFactor with hGolden | hConjugate
      · exact Or.inl (sub_eq_zero.mp hGolden)
      · exact Or.inr (sub_eq_zero.mp hConjugate)
    · rintro (rfl | rfl)
      · exact Real.goldenRatio_sq
      · exact Real.goldenConj_sq
  have hFixedPoints : ∀ z : Real, goldenMobius z = z ↔
      z = Real.goldenRatio ∨ z = Real.goldenConj := by
    intro z
    constructor
    · intro hFixed
      have hz : z ≠ 0 := by
        intro hZero
        subst z
        norm_num [goldenMobius] at hFixed
      exact (hRoots z).1 ((hFixedQuadratic z hz).1 hFixed)
    · rintro (rfl | rfl)
      · exact golden_mobius_fixed_golden
      · exact golden_mobius_fixed_conjugate
  have hConjugateForms :
      Real.goldenConj = 1 - Real.goldenRatio ∧
        Real.goldenConj = -(Real.goldenRatio⁻¹) := by
    constructor
    · exact Real.one_sub_goldenConj.symm
    · rw [Real.inv_goldenRatio]
      ring
  have hNonzero : Real.goldenRatio ≠ 0 ∧ Real.goldenConj ≠ 0 :=
    ⟨Real.goldenRatio_ne_zero, Real.goldenConj_ne_zero⟩
  have hFixedWitnesses :
      goldenMobius Real.goldenRatio = Real.goldenRatio ∧
        goldenMobius Real.goldenConj = Real.goldenConj :=
    ⟨golden_mobius_fixed_golden, golden_mobius_fixed_conjugate⟩
  have hNonfixedWitness : goldenMobius 1 = 2 ∧ goldenMobius 1 ≠ 1 := by
    norm_num [goldenMobius]
  have hSquareFormula : ∀ z : Real, z ≠ 0 → z ≠ -1 →
      goldenMobius (goldenMobius z) = (2 * z + 1) / (z + 1) := by
    intro z hz hNegOne
    have hzPlusOne : z + 1 ≠ 0 := by
      intro hZero
      apply hNegOne
      linarith
    unfold goldenMobius
    field_simp [hz, hzPlusOne]
    ring
  have hMatrixSquare : fibonacciSubstitution ^ 2 = !![2, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fibonacciSubstitution, pow_two, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hMatrixData :
      Matrix.det fibonacciSubstitution = -1 ∧
        Matrix.det (fibonacciSubstitution ^ 2) = 1 ∧
        Matrix.trace (fibonacciSubstitution ^ 2) = 3 := by
    refine ⟨fibonacci_substitution_trace_det_discriminant.2.1, ?_, ?_⟩
    · rw [hMatrixSquare, Matrix.det_fin_two]
      norm_num
    · rw [hMatrixSquare, Matrix.trace_fin_two]
      norm_num
  have hSqrtSquare : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hGoldenCenter : Real.goldenRatio - 1 / 2 = Real.sqrt 5 / 2 := by
    nlinarith [Real.goldenRatio_add_goldenConj,
      Real.goldenRatio_sub_goldenConj]
  have hConjugateCenter : Real.goldenConj - 1 / 2 = -(Real.sqrt 5 / 2) := by
    nlinarith [Real.goldenRatio_add_goldenConj,
      Real.goldenRatio_sub_goldenConj]
  have hAxisData :
      goldenAxisCircle Real.goldenRatio 0 ∧
        goldenAxisCircle Real.goldenConj 0 ∧
        goldenAxisCircle (1 / 2) (Real.sqrt 5 / 2) ∧
        0 < Real.sqrt 5 / 2 := by
    constructor
    · unfold goldenAxisCircle
      rw [hGoldenCenter]
      nlinarith
    constructor
    · unfold goldenAxisCircle
      rw [hConjugateCenter]
      nlinarith
    constructor
    · unfold goldenAxisCircle
      norm_num
      nlinarith
    · positivity
  have hExpPositive :
      Real.exp (2 * Real.log Real.goldenRatio) =
        Real.goldenRatio ^ 2 := by
    rw [show 2 * Real.log Real.goldenRatio =
      Real.log Real.goldenRatio + Real.log Real.goldenRatio by ring,
      Real.exp_add, Real.exp_log Real.goldenRatio_pos]
    ring
  have hExpNegative :
      Real.exp (-(2 * Real.log Real.goldenRatio)) =
        (Real.goldenRatio⁻¹) ^ 2 := by
    rw [show -(2 * Real.log Real.goldenRatio) =
      -Real.log Real.goldenRatio + -Real.log Real.goldenRatio by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log Real.goldenRatio_pos]
    ring
  have hCosh :
      Real.cosh (2 * Real.log Real.goldenRatio) = 3 / 2 := by
    rw [Real.cosh_eq, hExpPositive, hExpNegative,
      Real.inv_goldenRatio]
    nlinarith [Real.goldenRatio_sq, Real.goldenConj_sq,
      Real.goldenRatio_add_goldenConj]
  have hArcosh :
      Real.arcosh (3 / 2) = 2 * Real.log Real.goldenRatio := by
    rw [← hCosh]
    exact Real.arcosh_cosh
      (le_of_lt (mul_pos (by norm_num)
        (Real.log_pos Real.one_lt_goldenRatio)))
  have hLength :
      goldenAxisTranslationLength = 4 * Real.log Real.goldenRatio := by
    unfold goldenAxisTranslationLength
    rw [hArcosh]
    ring
  have hHalfLength :
      goldenAxisTranslationLength / 2 = goldenScalePeriod := by
    rw [hLength]
    unfold goldenScalePeriod
    ring
  have hLogIndex : goldenScalePeriod = Real.log goldenObserverIndex := by
    unfold goldenScalePeriod goldenObserverIndex
    rw [Real.log_pow]
    norm_num
  have hExpWeight :
      Real.exp (-goldenAxisTranslationLength / 2) =
        goldenProjectionWeight := by
    rw [show -goldenAxisTranslationLength / 2 =
      -(goldenAxisTranslationLength / 2) by ring, hHalfLength]
    unfold goldenScalePeriod goldenProjectionWeight
    exact hExpNegative
  have hAbsWeight :
      |goldenProjectiveMultiplier| = goldenProjectionWeight := by
    unfold goldenProjectionWeight
    exact abs_golden_projective_multiplier
  exact
    ⟨hFixedQuadratic, hRoots, hFixedPoints, hConjugateForms, hNonzero,
      hFixedWitnesses, hNonfixedWitness, hSquareFormula, hMatrixSquare,
      hMatrixData, hAxisData, rfl, rfl, hLength, hHalfLength, hLogIndex,
      hExpWeight, hAbsWeight⟩

#print axioms golden_hyperbolic_axis

end D5.S3.Observer.GoldenCoding.GoldenHyperbolicAxis
