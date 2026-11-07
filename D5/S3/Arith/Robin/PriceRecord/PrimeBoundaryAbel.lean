/- GID: D5/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PrimeBoundaryAbel
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Finite Abel suppliers with both endpoints and only ordinary PNT control. -/

import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.NumberTheory.AbelSummation

/-! Minimal finite real-endpoint Abel provider. The strict lower endpoint is represented by `Ioc`; the finite identity retains both endpoint terms. -/

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.PrimeBoundaryAbel

open Real Finset Filter MeasureTheory
open scoped Topology Chebyshev

def primeCount (t : ℝ) : ℝ := (Nat.primeCounting ⌊t⌋₊ : ℝ)

def primeInterval (y z : ℝ) : Finset ℕ :=
  (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime

def squareSum (y z : ℝ) : ℝ :=
  ∑ p ∈ primeInterval y z, 1 / (p : ℝ) ^ 2

private lemma prime_indicator_sum (t : ℝ) :
    (∑ p ∈ Icc 0 ⌊t⌋₊, if p.Prime then (1 : ℝ) else 0) = primeCount t := by
  classical
  rw [← sum_filter, ← Nat.primesLE_eq_filter_Icc_zero]
  simp only [sum_const, nsmul_eq_mul, mul_one, primeCount,
    Nat.primesLE_card_eq_primeCounting]

private lemma count_weight_integrable {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc y z)) :
    IntervalIntegrable (fun t => f t * primeCount t) volume y z := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hyz).mpr
  have hi := integrableOn_mul_sum_Icc
    (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) hy hf.integrableOn_Icc (m := 0)
  simpa only [prime_indicator_sum] using hi

/-- Exact finite partial summation, with strict lower endpoint (y,z].
The prime-counting endpoint terms are retained, even when y or z is prime. -/
theorem finite_prime_square_abel {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    squareSum y z = primeCount z / z ^ 2 - primeCount y / y ^ 2 +
      2 * (∫ t in y..z, primeCount t / t ^ 3) := by
  classical
  let c : ℕ → ℝ := fun p => if p.Prime then 1 else 0
  let f : ℝ → ℝ := fun t => 1 / t ^ 2
  have hd (t : ℝ) (ht : t ∈ Set.Icc y z) : HasDerivAt f (-2 / t ^ 3) t := by
    have ht0 : t ≠ 0 := (hy.trans_le ht.1).ne'
    convert (hasDerivAt_const t (1 : ℝ)).fun_div ((hasDerivAt_id t).pow 2)
      (pow_ne_zero 2 ht0) using 1 <;> dsimp [f] <;> field_simp <;> ring
  have hc : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc y z) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero _ (hy.trans_le ht.1).ne')
  have hi : IntegrableOn (deriv f) (Set.Icc y z) :=
    hc.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c hy.le hyz
    (fun t ht => (hd t ht).differentiableAt) hi
  have hcount (t : ℝ) : (∑ p ∈ Icc 0 ⌊t⌋₊, c p) = primeCount t :=
    prime_indicator_sum t
  simp_rw [hcount] at h
  rw [← intervalIntegral.integral_of_le hyz] at h
  have hs : (∑ p ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, f p * c p) = squareSum y z := by
    simp only [squareSum, primeInterval, sum_filter, c, f, mul_ite, mul_one, mul_zero]
  have hint : (∫ t in y..z, deriv f t * primeCount t) =
      -2 * (∫ t in y..z, primeCount t / t ^ 3) := by
    calc
      _ = ∫ t in y..z, (-2 : ℝ) * (primeCount t / t ^ 3) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hyz] at ht
        rw [(hd t ht).deriv]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hs, hint] at h
  calc
    squareSum y z = f z * primeCount z - f y * primeCount y -
        (-2 * (∫ t in y..z, primeCount t / t ^ 3)) := h
    _ = _ := by dsimp [f]; ring


end D5.S3.Arith.Robin.PriceRecord.PrimeBoundaryAbel
