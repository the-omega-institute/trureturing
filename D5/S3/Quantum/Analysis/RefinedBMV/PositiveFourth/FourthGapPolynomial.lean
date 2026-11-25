/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FourthGapPolynomial
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer polynomial formulas for the three four-copy gap multiplicity patterns. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FourGapPowerSeries
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.LinearCombination

/-! Polynomial numerators obtained by substituting fourth roots in the cleared partial fractions. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

section Polynomial

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 6] [OfNat R 12]

/-- Polynomial numerator for a triple eigenvalue and a single eigenvalue.
The powered roots are evaluated at the first degree. -/
def threeOnePolynomial (p a b u v : R) : R :=
  3*a*(a-b)^2*u^4*(p+1)*(p+2) - 6*a*b*(a-b)*u^4*(p+1) +
    6*a*b^2*u^4 - 6*b^3*v^4 - (a-b)^3*(p+1)*(p+2)*(p+3)*u^3*v

/-- Polynomial numerator for two repeated eigenvalues. -/
def twoTwoPolynomial (p a b u v : R) : R :=
  6*a^2*(a-b)*u^4*(p+1) - 12*a^2*b*u^4 +
    6*b^2*(a-b)*v^4*(p+1) + 12*b^2*a*v^4 -
    (a-b)^3*(p+1)*(p+2)*(p+3)*u^2*v^2

/-- Polynomial numerator for one repeated and two single eigenvalues. -/
def twoOneOnePolynomial (p a b c u v w : R) : R :=
  6*a^2*(a-b)*(a-c)*(b-c)*u^4*(p+1) -
    6*a^2*(b*(a-c)+c*(a-b))*(b-c)*u^4 +
    6*b^3*(a-c)^2*v^4 - 6*c^3*(a-b)^2*w^4 -
    ((a-b)^2*(a-c)^2*(b-c))*(p+1)*(p+2)*(p+3)*u^2*v*w

end Polynomial

private theorem cast_gaps_card (p : ℕ) :
    ((FourCopyGap.gaps p).card : ℝ) = (p+1)*(p+2)*(p+3)/6 := by
  rw [FourCopyGap.gaps_card]
  have h := Nat.add_one_mul_choose_eq (p+2) 2
  have h' : ((p:ℝ)+3) * ((p+2).choose 2 : ℝ) = 3 * ((p+3).choose 3 : ℝ) := by
    exact_mod_cast (by simpa [add_assoc, mul_comm] using h :
      (p+3) * (p+2).choose 2 = 3 * (p+3).choose 3)
  rw [Nat.cast_choose_two ℝ, Nat.cast_add] at h'
  linear_combination -(1 / 3 : ℝ) * h'

private theorem fourth_rpow (p : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (r^4)^((p:ℝ)/4) = r^p := by
  rw [← Real.rpow_natCast_mul hr,
    show ((4 : ℕ) : ℝ) * ((p : ℝ) / 4) = (p : ℝ) by push_cast; ring,
    Real.rpow_natCast]

open private FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

theorem threeOnePolynomial_eq (p : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    threeOnePolynomial (p:ℝ) (r^4) (t^4) (r^p) (t^p) =
      6 * (r^4-t^4)^3 * FourCopyGap.gapDefect p (r^4) (r^4) (r^4) (t^4) := by
  have h := cleared_gap_three_one p (r^4) (t^4)
  rw [FourCopyGap.balanced, fourth_rpow p hr, fourth_rpow p ht,
    Nat.cast_choose_two ℝ, cast_gaps_card p, pow_right_comm r 4 p,
    pow_right_comm t 4 p] at h
  push_cast at h
  unfold threeOnePolynomial
  linear_combination -6 * h

theorem twoTwoPolynomial_eq (p : ℕ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    twoTwoPolynomial (p:ℝ) (r^4) (t^4) (r^p) (t^p) =
      6 * (r^4-t^4)^3 * FourCopyGap.gapDefect p (r^4) (r^4) (t^4) (t^4) := by
  have h := cleared_gap_two_two p (r^4) (t^4)
  rw [FourCopyGap.balanced, fourth_rpow p hr, fourth_rpow p ht] at h
  rw [cast_gaps_card p, pow_right_comm r 4 p, pow_right_comm t 4 p] at h
  unfold twoTwoPolynomial
  linear_combination -6 * h

theorem twoOneOnePolynomial_eq (p : ℕ) {r t u : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    twoOneOnePolynomial (p:ℝ) (r^4) (t^4) (u^4) (r^p) (t^p) (u^p) =
      6 * ((r^4-t^4)^2*(r^4-u^4)^2*(t^4-u^4)) *
        FourCopyGap.gapDefect p (r^4) (r^4) (t^4) (u^4) := by
  have h := cleared_gap_two_one_one p (r^4) (t^4) (u^4)
  rw [FourCopyGap.balanced, fourth_rpow p hr, fourth_rpow p ht, fourth_rpow p hu] at h
  rw [cast_gaps_card p, pow_right_comm r 4 p, pow_right_comm t 4 p,
    pow_right_comm u 4 p] at h
  unfold twoOneOnePolynomial
  linear_combination -6 * h

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
