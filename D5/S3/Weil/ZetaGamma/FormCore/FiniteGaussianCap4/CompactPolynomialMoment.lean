/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactPolynomialMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The actual signed compact Laguerre integrals equal rational coefficient contractions of H and J. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactDebitMoment
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfRational
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set Polynomial
open scoped BigOperators

/-- Every rational polynomial may be integrated against the actual signed
compact debit weight by contracting its coefficients with the actual moments.
Integrability is proved for the discontinuous weight, not assumed. -/
theorem compact_polynomial_integral (q : ℚ[X]) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) * (q.map (Rat.castHom ℝ)).eval x) volume 0 6 ∧
    (∫ x : ℝ in 0..6,
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) * (q.map (Rat.castHom ℝ)).eval x) =
      ∑ m ∈ q.support, (q.coeff m : ℝ) * debitMoment m := by
  let w : ℝ → ℝ := fun x =>
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x * Real.exp (-2 * x)
  have heval (x : ℝ) : (q.map (Rat.castHom ℝ)).eval x =
      ∑ m ∈ q.support, (q.coeff m : ℝ) * x ^ m := by
    simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rfl
  have heq : (fun x : ℝ => w x * (q.map (Rat.castHom ℝ)).eval x) =
      (fun x : ℝ =>
        ∑ m ∈ q.support, (q.coeff m : ℝ) * (w x * x ^ m)) := by
    funext x
    rw [heval, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hi (m : ℕ) : IntervalIntegrable
      (fun x : ℝ => (q.coeff m : ℝ) * (w x * x ^ m)) volume 0 6 :=
    (debitMoment_formula m).1.const_mul (q.coeff m : ℝ)
  constructor
  · change IntervalIntegrable
      (fun x : ℝ => w x * (q.map (Rat.castHom ℝ)).eval x) volume 0 6
    rw [heq]
    convert (IntervalIntegrable.sum q.support (fun m _ => hi m)) using 1
    ext x
    simp only [Finset.sum_apply]
  · change (∫ x : ℝ in 0..6, w x * (q.map (Rat.castHom ℝ)).eval x) = _
    rw [heq, intervalIntegral.integral_finsetSum (fun m _ => hi m)]
    simp only [intervalIntegral.integral_const_mul, debitMoment, w]

/-- The original even Laguerre products with their physical argument 2*x
have an exact signed compact integral, reduced to H and J. The rational
polynomial already contains the powers of two, so no scale is inserted into
the moment contraction afterward. -/
theorem compact_laguerre_product_integral (i j : ℕ) :
    let q := FiniteGaussianCap4.LaguerreSevenHalf.RationalModel.evenProductQ i j
    IntervalIntegrable (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) *
        (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * i)).eval (2 * x) *
        (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * j)).eval (2 * x))
      volume 0 6 ∧
    (∫ x : ℝ in 0..6,
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        Real.exp (-2 * x) *
        (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * i)).eval (2 * x) *
        (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * j)).eval (2 * x)) =
      ∑ m ∈ q.support, (q.coeff m : ℝ) *
        (H m / 10 - J (m + 6) / (Real.pi ^ 2 * Real.sqrt Real.pi) +
          (4 * Real.pi ^ 3 * Real.sqrt Real.pi) * J m) := by
  dsimp only
  let q := FiniteGaussianCap4.LaguerreSevenHalf.RationalModel.evenProductQ i j
  have hp := compact_polynomial_integral q
  have heq :
      (fun x : ℝ =>
        x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
          Real.exp (-2 * x) *
          (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * i)).eval (2 * x) *
          (FiniteGaussianCap4.LaguerreSevenHalf.laguerre (2 * j)).eval (2 * x)) =
      (fun x : ℝ =>
        x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
          Real.exp (-2 * x) * (q.map (Rat.castHom ℝ)).eval x) := by
    funext x
    rw [FiniteGaussianCap4.LaguerreSevenHalf.RationalModel.evenProductQ_eval]
    ring
  constructor
  · rw [heq]
    exact hp.1
  · rw [heq, hp.2]
    apply Finset.sum_congr rfl
    intro m _
    rw [(debitMoment_formula m).2]

end FiniteGaussianCap475
