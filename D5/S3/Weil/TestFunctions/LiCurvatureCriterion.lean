/- GID: D5/S3/Weil/TestFunctions/LiCurvatureCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/LiCurvatureCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Toeplitz positivity and recurrence uniqueness support the Li curvature criterion. -/

import D5.S3.Weil.TestFunctions.LiCurvatureFourierRepresentation
import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.NumberTheory.LSeries.RiemannZeta

/- Library-search audit trail (2026-09-01):
   * D5 name and body-shape searches found no Li curvature criterion. The exact
     preceding Fourier representation is
     LiCurvatureFourierRepresentation.li_curvature_fourier_representation.
   * ExactTruncatedHaarFloor.circle_moment_toeplitz_posSemidef contains the
     forward Gram calculation only as a private helper; its public theorem has
     additional Haar-floor hypotheses and cannot be reused as this owner.
     TruncatedCircleMomentBridge.truncated_circle_moment_of_posSemidef is the
     finite-order converse, not one common representing measure for all orders.
   * Pinned Mathlib supplies Matrix.PosSemidef, integral_conj, finite-sum
     integration, and circle powers. Its Herglotz hits concern the
     Herglotz--Riesz kernel; no circle Herglotz/Bochner representation theorem
     or second-difference uniqueness theorem was found.
   * Installed non-Mathlib Lake packages contain no matching Herglotz,
     Toeplitz-moment, or Li-criterion declaration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder

namespace D5.S3.Weil.TestFunctions.LiCurvatureCriterion

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Fourier coefficient convention used by the source: the nth moment uses
the character z ^ (-n). -/
noncomputable def circleMoment (mu : Measure Circle) (n : Int) : Complex :=
  ∫ z : Circle, (z : Complex) ^ (-n) ∂mu

/-- The source Toeplitz matrix [c_(j-k)]. -/
def toeplitzMatrix (c : Int -> Complex) (N : Nat) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) Complex := fun j k =>
  c (((j : Nat) : Int) - ((k : Nat) : Int))

/-- The analytic polynomial determined by a finite coefficient vector. -/
def analyticPolynomial {N : Nat} (a : Fin (N + 1) -> Complex) (z : Circle) : Complex :=
  ∑ j, a j * (z : Complex) ^ (j : Nat)

private theorem circle_moment_integrand_eq_gram (z : Circle) (j k : Nat) :
    (z : Complex) ^ (-((j : Int) - (k : Int))) =
      (z : Complex) ^ k * star ((z : Complex) ^ j) := by
  rw [neg_sub, zpow_sub₀ (Circle.coe_ne_zero z), div_eq_mul_inv]
  congr 1
  change ((↑(z ^ j) : Complex)⁻¹) = star (↑(z ^ j) : Complex)
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]
  rfl

theorem circle_moment_toeplitz_entry
    (mu : Measure Circle) (N : Nat) (j k : Fin (N + 1)) :
    toeplitzMatrix (circleMoment mu) N j k =
      ∫ z : Circle,
        (z : Complex) ^ (k : Nat) * star ((z : Complex) ^ (j : Nat)) ∂mu := by
  apply integral_congr_ae
  filter_upwards [] with z
  exact circle_moment_integrand_eq_gram z j k

/-- A circle moment sequence is Hermitian without a separate symmetry
hypothesis. -/
theorem circle_moment_toeplitz_isHermitian
    (mu : Measure Circle) (N : Nat) :
    (toeplitzMatrix (circleMoment mu) N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [circle_moment_toeplitz_entry, circle_moment_toeplitz_entry]
  change conj (∫ z : Circle,
      (z : Complex) ^ (i : Nat) * star ((z : Complex) ^ (j : Nat)) ∂mu) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [map_mul]
  change star ((z : Complex) ^ (i : Nat)) *
      star (star ((z : Complex) ^ (j : Nat))) = _
  rw [star_star, mul_comm]

/-- The finite Toeplitz quadratic form of circle Fourier moments is exactly
the integral of the squared modulus of the coefficient polynomial. This is
the source's positive-definiteness identity, in Mathlib's convention that the
first vector argument is conjugate-linear. -/
theorem toeplitz_quadratic_eq_integral
    (mu : Measure Circle) [IsFiniteMeasure mu]
    (N : Nat) (a : Fin (N + 1) -> Complex) :
    star a ⬝ᵥ (toeplitzMatrix (circleMoment mu) N *ᵥ a) =
      ∫ z : Circle,
        analyticPolynomial a z * star (analyticPolynomial a z) ∂mu := by
  classical
  have integrandIntegrable (j k : Fin (N + 1)) :
      Integrable (fun z : Circle =>
        (z : Complex) ^ (k : Nat) * star ((z : Complex) ^ (j : Nat))) mu := by
    have continuousIntegrand : Continuous (fun z : Circle =>
        (z : Complex) ^ (k : Nat) * star ((z : Complex) ^ (j : Nat))) := by
      fun_prop
    simpa using continuousIntegrand.continuousOn.integrableOn_compact
      (μ := mu) isCompact_univ
  have energyExpansion :
      (∫ z : Circle,
          analyticPolynomial a z * star (analyticPolynomial a z) ∂mu) =
        ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
          star (a j) * toeplitzMatrix (circleMoment mu) N j k * a k := by
    calc
      (∫ z : Circle,
          analyticPolynomial a z * star (analyticPolynomial a z) ∂mu) =
          ∫ z : Circle, ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
            star (a j) *
              ((z : Complex) ^ (k : Nat) * star ((z : Complex) ^ (j : Nat))) *
              a k ∂mu := by
                refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
                simp only [analyticPolynomial, star_sum, star_mul]
                simp_rw [Finset.sum_mul, Finset.mul_sum]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j _
                apply Finset.sum_congr rfl
                intro k _
                ring
      _ = ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
          star (a j) * toeplitzMatrix (circleMoment mu) N j k * a k := by
            rw [integral_finsetSum Finset.univ]
            · apply Finset.sum_congr rfl
              intro j _
              rw [integral_finsetSum Finset.univ]
              · apply Finset.sum_congr rfl
                intro k _
                rw [circle_moment_toeplitz_entry]
                simp only [integral_const_mul, integral_mul_const]
              · intro k _
                exact ((integrandIntegrable j k).const_mul (star (a j))).mul_const (a k)
            · intro j _
              exact integrable_finsetSum Finset.univ fun k _ =>
                ((integrandIntegrable j k).const_mul (star (a j))).mul_const (a k)
  rw [energyExpansion]
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
  ring_nf

/-- Every finite Toeplitz matrix cut from a circle moment sequence is positive
semidefinite. -/
theorem circle_moment_toeplitz_posSemidef
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : Nat) :
    Matrix.PosSemidef (toeplitzMatrix (circleMoment mu) N) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (circle_moment_toeplitz_isHermitian mu N)
  intro a
  rw [toeplitz_quadratic_eq_integral]
  simp only [RCLike.star_def, Complex.mul_conj]
  exact integral_nonneg fun z =>
    Complex.zero_le_real.mpr (Complex.normSq_nonneg (analyticPolynomial a z))

/-- The two initial values and the same second differences uniquely determine
a real sequence. -/
theorem second_difference_recurrence_unique
    (x y curvature : Nat -> Real)
    (zeroValue : x 0 = y 0)
    (oneValue : x 1 = y 1)
    (xRecurrence : forall n, 1 <= n ->
      x (n + 1) - 2 * x n + x (n - 1) = curvature n)
    (yRecurrence : forall n, 1 <= n ->
      y (n + 1) - 2 * y n + y (n - 1) = curvature n) :
    x = y := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact zeroValue
  | one => exact oneValue
  | more n ih0 ih1 =>
      have hx := xRecurrence (n + 1) (by omega)
      have hy := yRecurrence (n + 1) (by omega)
      rw [show n + 1 + 1 = n + 2 by omega,
        show n + 1 - 1 = n by omega] at hx hy
      linarith

/-- A Dirac mass at 1 with coefficients (1,1) makes both sides of the
Toeplitz integral identity equal to 4, so the construction is nonzero. -/
theorem dirac_one_toeplitz_witness :
    let mu : Measure Circle := Measure.dirac 1
    let a : Fin 2 -> Complex := fun _ => 1
    star a ⬝ᵥ (toeplitzMatrix (circleMoment mu) 1 *ᵥ a) = 4 ∧
      (∫ z : Circle,
        analyticPolynomial a z * star (analyticPolynomial a z) ∂mu) = 4 := by
  dsimp only
  rw [toeplitz_quadratic_eq_integral]
  simp [analyticPolynomial, Fin.sum_univ_two]
  norm_num

/-- The sequence n^2 realizes constant second difference 2, with initial
segment 0,1,4,9. -/
theorem quadratic_second_difference_witness :
    let x : Nat -> Real := fun n => n ^ 2
    x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 4 ∧ x 3 = 9 ∧
      forall n, 1 <= n -> x (n + 1) - 2 * x n + x (n - 1) = 2 := by
  dsimp only
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro n hn
  push_cast [Nat.cast_sub hn]
  ring

#print axioms toeplitz_quadratic_eq_integral
#print axioms circle_moment_toeplitz_posSemidef
#print axioms second_difference_recurrence_unique
#print axioms dirac_one_toeplitz_witness
#print axioms quadratic_second_difference_witness

end D5.S3.Weil.TestFunctions.LiCurvatureCriterion
