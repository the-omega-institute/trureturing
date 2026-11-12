/- GID: D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial
   mirror-E: none(waiver:actual-ordinary-avoider-peak-polynomial)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.BigOperators]
   utility: none
   digest: The weighted polynomial of actual ordinary avoiders equals the actual Dyck peak polynomial. -/

import D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanStatistics
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Finite weighted sums over the actual carriers connect the proved bijection
to polynomial coefficients. These are coefficient polynomials, not a proof of
the still separate formal-series equation or Lagrange inversion over Q[y]. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanPolynomial

open OrdinaryAscentSemantics OrdinaryAscentCatalanRank OrdinaryAscentCatalanStatistics
open D5.S3.Combinatorics.Permutation.MultisetRookEulerianInterlacingRefutation (asc)
open Polynomial

/-- Sum the complementary-ascent monomial over actual ordinary literal avoiders. -/
def wordPeakPolynomial (n : ℕ) : ℕ[X] :=
  letI := (avoiders_finite n {.p101, .p201}).fintype
  ∑ w : avoiders n {.p101, .p201}, X ^ (n - asc w.val)

/-- Sum the adjacent-UD peak monomial over actual Mathlib Dyck words. -/
def dyckPeakPolynomial (n : ℕ) : ℕ[X] :=
  ∑ p : {p : DyckWord // p.semilength = n}, X ^ p.val.peakCount

/-- The actual equivalence transports the entire finite weighted polynomial. -/
theorem wordPeakPolynomial_eq (n : ℕ) :
    wordPeakPolynomial n = dyckPeakPolynomial n := by
  classical
  letI := (avoiders_finite n {.p101, .p201}).fintype
  unfold wordPeakPolynomial dyckPeakPolynomial
  apply Fintype.sum_equiv (dyckEquiv n)
  intro w
  rw [dyckEquiv_peaks]

/-- Each Dyck peak-polynomial coefficient counts its actual statistic fiber. -/
theorem coeff_dyckPeakPolynomial (n k : ℕ) :
    (dyckPeakPolynomial n).coeff k =
      Fintype.card {p : {p : DyckWord // p.semilength = n} // p.val.peakCount = k} := by
  classical
  simp [dyckPeakPolynomial, finsetSum_coeff, coeff_X_pow, Fintype.card_subtype, eq_comm]

/-- The actual ordinary-word polynomial has the licensed Narayana coefficients,
with the exceptional zero-peak natural quotient explicitly excluded. -/
theorem coeff_wordPeakPolynomial (n k : ℕ) (h : ¬ (n = 1 ∧ k = 0)) :
    (wordPeakPolynomial n).coeff k = Nat.narayana n k := by
  rw [wordPeakPolynomial_eq, coeff_dyckPeakPolynomial,
    DyckWord.card_semilength_peakCount n k h]

/-- The exceptional actual coefficient is zero, despite the natural quotient. -/
theorem coeff_one_zero : (wordPeakPolynomial 1).coeff 0 = 0 := by
  rw [wordPeakPolynomial_eq, coeff_dyckPeakPolynomial,
    DyckWord.card_semilength_one_peakCount_zero]

/-- Evaluation at one recovers the actual Catalan total at every length. -/
theorem eval_one (n : ℕ) : (wordPeakPolynomial n).eval 1 = catalan n := by
  rw [wordPeakPolynomial_eq]
  simp only [dyckPeakPolynomial, eval_finsetSum, eval_pow, eval_X, one_pow]
  simpa using DyckWord.card_dyckWord_semilength_eq_catalan n

end D5.S3.Combinatorics.OrdinaryAscent.OrdinaryAscentCatalanPolynomial
