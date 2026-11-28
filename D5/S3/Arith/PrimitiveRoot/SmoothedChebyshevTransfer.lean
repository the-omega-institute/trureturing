/- GID: D5/S3/Arith/PrimitiveRoot/SmoothedChebyshevTransfer
   generality: I
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/SmoothedChebyshevTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite-interval transfer from the integrated Mangoldt remainder to smoothed Chebyshev error. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open scoped BigOperators Interval

namespace D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer

open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.IntegratedExplicit
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes (psi1)

private theorem ramp_integral {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hnx : (n : ℝ) ≤ x) :
    (∫ t in (1 : ℝ)..x, mangoldtRamp n t) =
      ArithmeticFunction.vonMangoldt n * (x - n) ^ 2 / (2 * n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi := mangoldtRamp_continuous n
  have hz : (∫ t in (1 : ℝ)..(n : ℝ), mangoldtRamp n t) = 0 := by
    calc
      _ = ∫ _t in (1 : ℝ)..(n : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hn1] at ht
        simp only [mangoldtRamp, max_eq_right (by
          have := (div_le_one hn0).mpr ht.2
          linarith : t / (n : ℝ) - 1 ≤ 0), mul_zero]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (n : ℝ))
    hi.intervalIntegrable hi.intervalIntegrable, hz, zero_add]
  have he : (∫ t in (n : ℝ)..x, mangoldtRamp n t) =
      ∫ t in (n : ℝ)..x, ArithmeticFunction.vonMangoldt n * (t / (n : ℝ) - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hnx] at ht
    exact ramp_eq_affine (by omega) ht.1
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_id.div_const _) intervalIntegrable_const,
    intervalIntegral.integral_div, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  field_simp [hn0.ne']
  <;> ring

private theorem part_eq_fixed_sum {x t : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    mangoldtPart t = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, mangoldtRamp n t := by
  apply tsum_eq_sum
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [mangoldtRamp]
  · have hfloor : ⌊x⌋₊ < n := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      omega
    exact ramp_zero_of_lt (by linarith) (htx.trans_lt (Nat.lt_of_floor_lt hfloor))

private theorem log_moment {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, t * Real.log t) =
      x ^ 2 / 2 * Real.log x - x ^ 2 / 4 + 1 / 4 := by
  have hpos : ∀ t ∈ uIcc (1 : ℝ) x, 0 < t := by
    rw [uIcc_of_le hx]
    intro t ht
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => t * Real.log t) (uIcc 1 x) := by
    apply continuousOn_id.mul
    exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (hpos t ht))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
    (f' := fun t : ℝ => t * Real.log t)
    (a := 1) (b := x) (fun t ht => by
      have ht0 := (hpos t ht).ne'
      convert ((((hasDerivAt_id t).pow 2).div_const 2).mul
        (Real.hasDerivAt_log ht0)).sub (((hasDerivAt_id t).pow 2).div_const 4) using 1
      field_simp
      <;> ring) hc.intervalIntegrable
  simpa using he

/-- The lower-endpoint correction makes the transfer valid also at x = 1. -/
theorem psi1_div_sub_half_eq_integrated_U {x : ℝ} (hx : 1 ≤ x) :
    psi1 x / x - x / 2 =
      U x - (2 / x) * (∫ t in (1 : ℝ)..x, U t) -
        (3 / 2 + Real.eulerMascheroniConstant) / x := by
  have hx0 : 0 < x := by linarith
  let s := Finset.Icc 1 ⌊x⌋₊
  have hsum : IntervalIntegrable (fun t : ℝ => ∑ n ∈ s, mangoldtRamp n t)
      volume 1 x := (continuous_finsetSum s fun n _ => mangoldtRamp_continuous n).intervalIntegrable
  have hlog : IntervalIntegrable (fun t : ℝ => t * Real.log t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.mul
    apply Real.continuousOn_log.mono
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact ne_of_gt (by linarith [ht.1])
  have hlin : IntervalIntegrable
      (fun t : ℝ => (1 + Real.eulerMascheroniConstant) * t) volume 1 x := by
    exact continuous_id.const_mul _ |>.intervalIntegrable
  have hi : (∫ t in (1 : ℝ)..x, U t) =
      (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (x - n) ^ 2 / (2 * n)) -
        (x ^ 2 / 2 * Real.log x - x ^ 2 / 4 + 1 / 4) +
        (1 + Real.eulerMascheroniConstant) * ((x ^ 2 - 1) / 2) := by
    calc
      _ = ∫ t in (1 : ℝ)..x,
          (∑ n ∈ s, mangoldtRamp n t) - t * Real.log t +
            (1 + Real.eulerMascheroniConstant) * t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hx] at ht
        rw [U_eq_complete_ramps (by linarith [ht.1]), part_eq_fixed_sum ht.1 ht.2]
      _ = _ := by
        rw [intervalIntegral.integral_add (hsum.sub hlog) hlin,
          intervalIntegral.integral_sub hsum hlog,
          intervalIntegral.integral_finsetSum (fun n _ => (mangoldtRamp_continuous n).intervalIntegrable),
          log_moment hx, intervalIntegral.integral_const_mul, integral_id]
        simp only [one_pow]
        congr 2
        apply Finset.sum_congr rfl
        intro n hn
        exact ramp_integral (Finset.mem_Icc.mp hn).1
          ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2)
  rw [U_eq_complete_ramps hx0.le, part_eq_fixed_sum hx le_rfl, hi,
    ConjectureMachines.Semantics.Riemann.WeightedStieltjes.psi1_eq_sum_Icc_sub_mul_vonMangoldt hx]
  have hs : (∑ n ∈ s, mangoldtRamp n x) -
      (2 / x) * (∑ n ∈ s, ArithmeticFunction.vonMangoldt n * (x - n) ^ 2 / (2 * n)) =
      (∑ n ∈ s, (x - n) * ArithmeticFunction.vonMangoldt n) / x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [ramp_eq_affine (by omega)
      ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2)]
    field_simp [hx0.ne', hn0]
    <;> ring
  dsimp only [s] at hs ⊢
  have hsmooth :
      (-(x * Real.log x) + (1 + Real.eulerMascheroniConstant) * x) -
      (2 / x) * (-(x ^ 2 / 2 * Real.log x - x ^ 2 / 4 + 1 / 4) +
        (1 + Real.eulerMascheroniConstant) * ((x ^ 2 - 1) / 2)) -
      (3 / 2 + Real.eulerMascheroniConstant) / x = -x / 2 := by
    field_simp [hx0.ne']
    <;> ring
  linear_combination -hs - hsmooth

end D5.S3.Arith.PrimitiveRoot.SmoothedChebyshevTransfer
