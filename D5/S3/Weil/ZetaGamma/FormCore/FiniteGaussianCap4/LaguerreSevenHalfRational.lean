/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfRational
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:fixed-alpha-laguerre-helper)
   anchors: []
   utility: none
   digest: Exact rational coefficient model for the alpha seven halves compact matrix certificate. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfPolynomial

/-! Rational coefficient model consumed by the actual compact matrix certificate.
The variable scaling 2*x is included before taking product coefficients. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf.RationalModel

def momentQ : ℕ → ℚ
  | 0 => 1
  | n + 1 => momentQ n * (9 / 2 + n)

@[simp] theorem momentQ_cast (n : ℕ) : (momentQ n : ℝ) = momentWeight n := by
  induction n with
  | zero => simp [momentQ]
  | succ n ih => simp [momentQ, momentWeight_succ, ih]

/-- The exact rational congruence scale consumed by the matrix certificate. -/
def congruenceScaleQ : ℕ → ℚ
  | 0 => 1
  | k + 1 => congruenceScaleQ k * ((k : ℚ) + 1 / 2) / ((k : ℚ) + 11 / 4)

def coefficientQ (n j : ℕ) : ℚ :=
  (-1) ^ j * (n.choose j : ℚ) * momentQ n /
    (momentQ j * (n.factorial : ℚ))

@[simp] theorem coefficientQ_cast (n j : ℕ) :
    (coefficientQ n j : ℝ) = coefficient n j := by
  simp [coefficientQ, coefficient]

def laguerreQ (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j (coefficientQ n j)

@[simp] theorem laguerreQ_map (n : ℕ) :
    (laguerreQ n).map (Rat.castHom ℝ) = laguerre n := by
  simp [laguerreQ, laguerre, Polynomial.map_sum]

def scaledLaguerreQ (n : ℕ) : ℚ[X] :=
  (laguerreQ n).comp (C 2 * X)

theorem scaledLaguerreQ_eval (n : ℕ) (x : ℝ) :
    ((scaledLaguerreQ n).map (Rat.castHom ℝ)).eval x =
      (laguerre n).eval (2 * x) := by
  simp [scaledLaguerreQ, Polynomial.map_comp]

def evenProductQ (i j : ℕ) : ℚ[X] :=
  scaledLaguerreQ (2 * i) * scaledLaguerreQ (2 * j)

theorem evenProductQ_eval (i j : ℕ) (x : ℝ) :
    ((evenProductQ i j).map (Rat.castHom ℝ)).eval x =
      (laguerre (2 * i)).eval (2 * x) * (laguerre (2 * j)).eval (2 * x) := by
  simp [evenProductQ, scaledLaguerreQ_eval]

/-- The actual product is symmetric before any certificate data is chosen. -/
theorem evenProductQ_symm (i j : ℕ) : evenProductQ i j = evenProductQ j i := by
  exact mul_comm _ _

end FiniteGaussianCap4.LaguerreSevenHalf.RationalModel

