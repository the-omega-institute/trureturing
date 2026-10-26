/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixCore
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual signed compact matrix entries and the polynomial integral operations used by their numeric certificates. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactPolynomialMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set Polynomial
open FiniteGaussianCap4.LaguerreSevenHalf
open FiniteGaussianCap4.LaguerreSevenHalf.RationalModel

/-- The signed compact polynomial moment is an actual interval integral. -/
def compactPolynomialMoment (q : ℚ[X]) : ℝ :=
  ∫ x : ℝ in 0..6,
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      Real.exp (-2 * x) * (q.map (Rat.castHom ℝ)).eval x

@[simp] theorem compactPolynomialMoment_zero : compactPolynomialMoment 0 = 0 := by
  simp [compactPolynomialMoment]

/-- Additivity uses the proved integrability of both actual summands. -/
theorem compactPolynomialMoment_add (p q : ℚ[X]) :
    compactPolynomialMoment (p + q) =
      compactPolynomialMoment p + compactPolynomialMoment q := by
  unfold compactPolynomialMoment
  simp only [Polynomial.map_add, Polynomial.eval_add, mul_add]
  exact intervalIntegral.integral_add
    (compact_polynomial_integral p).1 (compact_polynomial_integral q).1

/-- The monomial evaluator consumed by the entry certificate expressions. -/
theorem compactPolynomialMoment_monomial (m : ℕ) (a : ℚ) :
    compactPolynomialMoment (Polynomial.monomial m a) = (a : ℝ) * debitMoment m := by
  have heq :
      (fun x : ℝ =>
        x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
          Real.exp (-2 * x) *
          ((Polynomial.monomial m a).map (Rat.castHom ℝ)).eval x) =
      (fun x : ℝ => (a : ℝ) *
        (x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
          Real.exp (-2 * x) * x ^ m)) := by
    funext x
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial]
    change _ * ((a : ℝ) * x ^ m) = _
    ring
  unfold compactPolynomialMoment
  rw [heq]
  exact intervalIntegral.integral_const_mul (a : ℝ) _

/-- The common square normalization N_0^2 appearing in the actual matrix. -/
def normalizationSquared : ℝ := 256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi)

/-- Actual signed compact matrix in the specified rational congruence scales.
No entry enclosure or equality with a fitted center is part of this definition. -/
def compactMomentMatrix (i j : Fin 16) : ℝ :=
  normalizationSquared * (congruenceScaleQ i.val : ℝ) *
    (congruenceScaleQ j.val : ℝ) *
      compactPolynomialMoment (evenProductQ i.val j.val)

theorem compactMomentMatrix_symm (i j : Fin 16) :
    compactMomentMatrix i j = compactMomentMatrix j i := by
  unfold compactMomentMatrix
  rw [evenProductQ_symm i.val j.val]
  ring

/-- The matrix entries are the original Laguerre product integrals, with
argument 2*x and the same signed compact multiplier. -/
theorem compactMomentMatrix_integral (i j : Fin 16) :
    compactMomentMatrix i j =
      normalizationSquared * (congruenceScaleQ i.val : ℝ) *
        (congruenceScaleQ j.val : ℝ) *
        (∫ x : ℝ in 0..6,
          x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
            Real.exp (-2 * x) *
            (laguerre (2 * i.val)).eval (2 * x) *
            (laguerre (2 * j.val)).eval (2 * x)) := by
  unfold compactMomentMatrix compactPolynomialMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [evenProductQ_eval]
  ring

end FiniteGaussianCap475
