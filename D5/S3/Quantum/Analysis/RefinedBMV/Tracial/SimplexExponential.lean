/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SimplexExponential
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered-simplex exponential integration with a confluent endpoint. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exponential means on the four-coordinate simplex. -/

open MeasureTheory
open scoped Interval

namespace RefinedBMV.Tracial

noncomputable section

/-- Uniform exponential mean on four simplex weights, written in ordered
coordinates. The weights are w, v-w, u-v and 1-u. -/
def simplexExp (a b c d : ℝ) : ℝ :=
  6 * ∫ u in 0..1, ∫ v in 0..u, ∫ w in 0..v,
    Real.exp (d + (c - d) * u + (b - c) * v + (a - b) * w)

/-- The balanced deficit of the four-slot exponential simplex mean. -/
def simplexGap (a b c d : ℝ) : ℝ :=
  simplexExp a b c d - Real.exp ((a + b + c + d) / 4)

private def expPrimitive (r u : ℝ) : ℝ :=
  if r = 0 then u else (Real.exp (r * u) - 1) / r

private theorem exp_rate_intervalIntegrable (r u : ℝ) :
    IntervalIntegrable (fun x ↦ Real.exp (r * x)) volume 0 u :=
  (by fun_prop : Continuous (fun x ↦ Real.exp (r * x))).intervalIntegrable _ _

private theorem integral_exp_rate (r u : ℝ) :
    (∫ x in 0..u, Real.exp (r * x)) = expPrimitive r u := by
  by_cases hr : r = 0
  · simp [hr, expPrimitive]
  have hd (x : ℝ) : HasDerivAt (fun x ↦ Real.exp (r * x) / r)
      (Real.exp (r * x)) x := by
    convert (((hasDerivAt_id x).const_mul r).exp).div_const r using 1 <;>
      simp [id, hr]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    (exp_rate_intervalIntegrable r u)]
  simp only [expPrimitive, ite_eq_right hr, mul_zero, Real.exp_zero]
  ring

private theorem integral_exp_affine (q r u : ℝ) :
    (∫ x in 0..u, Real.exp (q + r * x)) = Real.exp q * expPrimitive r u := by
  simp_rw [Real.exp_add]
  rw [intervalIntegral.integral_const_mul, integral_exp_rate]

private theorem inner_integrals (a b c d u : ℝ) (hab : a ≠ b) :
    (∫ v in 0..u, ∫ w in 0..v,
      Real.exp (d + (c - d) * u + (b - c) * v + (a - b) * w)) =
      Real.exp (d + (c - d) * u) *
        (expPrimitive (a - c) u - expPrimitive (b - c) u) / (a - b) := by
  have h (v : ℝ) :
      Real.exp (d + (c - d) * u + (b - c) * v) * expPrimitive (a - b) v =
      Real.exp (d + (c - d) * u) / (a - b) *
        (Real.exp ((a - c) * v) - Real.exp ((b - c) * v)) := by
    simp only [expPrimitive, ite_eq_right (sub_ne_zero.mpr hab), Real.exp_add]
    rw [show Real.exp ((a-c)*v) = Real.exp ((b-c)*v) *
        Real.exp ((a-b)*v) by rw [← Real.exp_add]; congr 1; ring]
    ring
  simp_rw [integral_exp_affine, h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (exp_rate_intervalIntegrable _ _)
      (exp_rate_intervalIntegrable _ _),
    integral_exp_rate, integral_exp_rate]
  ring

private theorem integral_shifted_primitive (a c d : ℝ) (hac : a ≠ c) :
    (∫ u in 0..1, Real.exp (d + (c - d) * u) * expPrimitive (a - c) u) =
    Real.exp d * (expPrimitive (a - d) 1 - expPrimitive (c - d) 1) / (a - c) := by
  have h (u : ℝ) :
      Real.exp (d + (c - d) * u) * expPrimitive (a - c) u =
      Real.exp d / (a - c) *
        (Real.exp ((a - d) * u) - Real.exp ((c - d) * u)) := by
    simp only [expPrimitive, ite_eq_right (sub_ne_zero.mpr hac), Real.exp_add]
    rw [show Real.exp ((a-d)*u) = Real.exp ((c-d)*u) *
        Real.exp ((a-c)*u) by rw [← Real.exp_add]; congr 1; ring]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (exp_rate_intervalIntegrable _ _)
      (exp_rate_intervalIntegrable _ _),
    integral_exp_rate, integral_exp_rate]
  ring

private theorem simplexExp_eval_primitive (a b c d : ℝ) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    simplexExp a b c d =
      6 * Real.exp d / (a - b) *
        ((expPrimitive (a - d) 1 - expPrimitive (c - d) 1) / (a - c) -
          (expPrimitive (b - d) 1 - expPrimitive (c - d) 1) / (b - c)) := by
  have hint (r : ℝ) :
      IntervalIntegrable (fun u ↦ Real.exp (d + (c - d) * u) * expPrimitive r u)
        volume 0 1 := by
    by_cases hr : r = 0
    · simp only [expPrimitive, ite_eq_left hr]
      exact (by fun_prop : Continuous (fun u ↦
        Real.exp (d + (c - d) * u) * u)).intervalIntegrable _ _
    · simp only [expPrimitive, ite_eq_right hr]
      exact (by fun_prop : Continuous (fun u ↦ Real.exp (d + (c - d) * u) *
        ((Real.exp (r * u) - 1) / r))).intervalIntegrable _ _
  unfold simplexExp
  simp_rw [inner_integrals a b c d _ hab, mul_sub, div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub (hint _) (hint _),
    integral_shifted_primitive a c d hac, integral_shifted_primitive b c d hbc]
  ring

/-- First divided difference of the exponential, with its confluent value. -/
def expDividedDifference (a b : ℝ) : ℝ :=
  if a = b then Real.exp a else (Real.exp a - Real.exp b) / (a - b)

private theorem exp_mul_primitive (a d : ℝ) :
    Real.exp d * expPrimitive (a - d) 1 = expDividedDifference a d := by
  by_cases h : a = d
  · subst a
    simp [expPrimitive, expDividedDifference]
  have he : Real.exp d * Real.exp (a - d) = Real.exp a := by
    rw [← Real.exp_add, show d + (a - d) = a by ring]
  simp only [expPrimitive, expDividedDifference, ite_eq_right h,
    ite_eq_right (sub_ne_zero.mpr h), mul_one]
  rw [← mul_div_assoc, mul_sub, he, mul_one]

/-- The exponential simplex mean as a third divided difference. The last
two arguments may coincide, in which case the first difference is confluent. -/
theorem simplexExp_eval (a b c d : ℝ) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    simplexExp a b c d =
      6 / (a - b) *
        ((expDividedDifference a d - expDividedDifference c d) / (a - c) -
          (expDividedDifference b d - expDividedDifference c d) / (b - c)) := by
  rw [simplexExp_eval_primitive a b c d hab hac hbc, ← exp_mul_primitive a d,
    ← exp_mul_primitive b d, ← exp_mul_primitive c d]
  ring

theorem simplexGap_add (a b c d m : ℝ) :
    simplexGap (a + m) (b + m) (c + m) (d + m) =
      Real.exp m * simplexGap a b c d := by
  have hmean : (a + m + (b + m) + (c + m) + (d + m)) / 4 =
      m + (a + b + c + d) / 4 := by ring
  have he (u v w : ℝ) :
      d + m + (c + m - (d + m)) * u + (b + m - (c + m)) * v +
        (a + m - (b + m)) * w =
      m + (d + (c - d) * u + (b - c) * v + (a - b) * w) := by ring
  unfold simplexGap simplexExp
  simp_rw [hmean, he, Real.exp_add m, intervalIntegral.integral_const_mul]
  ring

end

end RefinedBMV.Tracial
