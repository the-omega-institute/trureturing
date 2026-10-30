/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/IntegerExpMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual compact exponential moments for the signed Gaussian certificate. -/
/-
Actual moment suppliers for the finite Gaussian signed multiplier.

Integer incomplete-exponential moments for the SAME finite Gaussian signed
multiplier. The endpoint formula is the standard finite incomplete-gamma
formula, also used in the completed independent_check.py (SHA256
f1e7c5aee8882415df524430ad3012a81b4c0ba6c5b68baa5aff41c82f75fcb5).
We prove it here by differentiating an explicit polynomial antiderivative.
No computation, expansion assumption, or target-integral hypothesis is used.
The theorem works for arbitrary real endpoints, hence for 0 < a <= b.
The adjacent proved endpoint boxes are imported for the later enclosure supplier.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianExpPiRounding
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Integer incomplete-exponential moments from an actual antiderivative. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap475
open MeasureTheory Set
open scoped BigOperators

/-- Explicit polynomial multiplying exp(-2 x) in the antiderivative. -/
def integerEndpointPolynomial (m : ℕ) (x : ℝ) : ℝ :=
  (m.factorial : ℝ) / (2 : ℝ) ^ (m + 1) *
    ∑ j ∈ Finset.range (m + 1), (2 * x) ^ j / (j.factorial : ℝ)

private theorem integerEndpointPolynomial_zero (x : ℝ) :
    integerEndpointPolynomial 0 x = 1 / 2 := by
  norm_num [integerEndpointPolynomial]

private theorem integerEndpointPolynomial_succ (m : ℕ) (x : ℝ) :
    integerEndpointPolynomial (m + 1) x =
      ((m : ℝ) + 1) / 2 * integerEndpointPolynomial m x + x ^ (m + 1) / 2 := by
  unfold integerEndpointPolynomial
  conv_lhs => rw [Finset.sum_range_succ]
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have ht : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow,
    pow_succ]
  field_simp [hm, hm1, ht]
  <;> ring

private theorem integerEndpointPolynomial_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt (integerEndpointPolynomial m)
      (2 * integerEndpointPolynomial m x - x ^ m) x := by
  induction m with
  | zero =>
    have hf : integerEndpointPolynomial 0 = (fun _ : ℝ => 1 / 2) :=
      funext integerEndpointPolynomial_zero
    simp only [hf]
    convert hasDerivAt_const x (1 / 2 : ℝ) using 1 <;> norm_num
  | succ m ih =>
    have hd := (ih.const_mul (((m : ℝ) + 1) / 2)).add
      (((hasDerivAt_id x).pow (m + 1)).div_const 2)
    convert hd using 1
    · exact funext (integerEndpointPolynomial_succ m)
    · rw [integerEndpointPolynomial_succ]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel_right, mul_one, id_eq]
      ring

private theorem integerPrimitive_hasDerivAt (m : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => -Real.exp (-2 * y) * integerEndpointPolynomial m y)
      (x ^ m * Real.exp (-2 * x)) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-2 * y))
      (Real.exp (-2 * x) * (-2)) x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (-2 : ℝ)).exp
  have hp := integerEndpointPolynomial_hasDerivAt m x
  convert he.neg.mul hp using 1 <;>
    simp only [Pi.neg_apply, Pi.mul_apply, id_eq] <;> first | rfl | ring

/-- Genuine continuous integrability and the integer endpoint formula.
No positivity premise is needed for integer powers on a compact interval. -/
theorem integerMoment_endpoint (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => x ^ m * Real.exp (-2 * x)) volume a b ∧
    (∫ x : ℝ in a..b, x ^ m * Real.exp (-2 * x)) =
      (m.factorial : ℝ) / (2 : ℝ) ^ (m + 1) *
        (Real.exp (-2 * a) *
          (∑ j ∈ Finset.range (m + 1), (2 * a) ^ j / (j.factorial : ℝ)) -
        Real.exp (-2 * b) *
          (∑ j ∈ Finset.range (m + 1), (2 * b) ^ j / (j.factorial : ℝ))) := by
  have hc : Continuous (fun x : ℝ => x ^ m * Real.exp (-2 * x)) := by fun_prop
  have hi : IntervalIntegrable (fun x : ℝ => x ^ m * Real.exp (-2 * x))
      volume a b := hc.intervalIntegrable a b
  refine ⟨hi, ?_⟩
  have hv := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun x _ => integerPrimitive_hasDerivAt m x) hi
  rw [hv]
  unfold integerEndpointPolynomial
  ring

/-- The actual J_m inputs in the signed multiplier matrix. -/
def J (m : ℕ) : ℝ := ∫ x : ℝ in Real.pi..6, x ^ m * Real.exp (-2 * x)

/-- In particular this supplies every J_m with m <= 66. This is an exact
analytic identity, without a claimed transcendental or rational enclosure. -/
theorem J_endpoint (m : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ m * Real.exp (-2 * x))
      volume Real.pi 6 ∧
    J m = (m.factorial : ℝ) / (2 : ℝ) ^ (m + 1) *
      (Real.exp (-2 * Real.pi) *
        (∑ j ∈ Finset.range (m + 1), (2 * Real.pi) ^ j / (j.factorial : ℝ)) -
      Real.exp (-12) *
        (∑ j ∈ Finset.range (m + 1), (12 : ℝ) ^ j / (j.factorial : ℝ))) := by
  simpa only [J, show -(2 : ℝ) * 6 = -12 by norm_num,
    show (2 : ℝ) * 6 = 12 by norm_num] using integerMoment_endpoint m Real.pi 6

end FiniteGaussianCap475
