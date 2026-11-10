/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingAverageIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forward substitution decomposes the average of a moving short increment. -/

import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Forward substitution for averages of moving short increments. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingAverageIdentity

open Set MeasureTheory
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Forward substitution expresses a moving increment average using fixed increments
and the derivative and endpoint corrections of the moving length. -/
theorem moving_average_forward_identity {E : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) {a s x M : ℝ}
    (ha : 0 < a) (hs : 0 ≤ s) (hx : 0 < x) (hM : 0 < M) :
    let L : ℝ → ℝ := fun y => s * y ^ a
    let L' : ℝ → ℝ := fun y => s * (a * y ^ (a - 1))
    let φ : ℝ → ℝ := movingShift a s
    let Q₀ := x + M + L x
    let δ := L (x + M) - L x
    M * windowAverage M (movingIncrement E a s) x =
      (∫ r in (0 : ℝ)..L x, increment E M (x + r)) -
      (∫ r in (0 : ℝ)..M, L' (x + r) * (E (φ (x + r)) - E x)) +
      ∫ v in (0 : ℝ)..δ, E (Q₀ + v) - E x := by
  dsimp only
  let L : ℝ → ℝ := fun y => s * y ^ a
  let L' : ℝ → ℝ := fun y => s * (a * y ^ (a - 1))
  let φ : ℝ → ℝ := movingShift a s
  let P := x + L x
  let Q₀ := x + M + L x
  let Q := x + M + L (x + M)
  let δ := L (x + M) - L x
  have hL : Continuous L := continuous_const.mul (Real.continuous_rpow_const ha.le)
  have hφ : Continuous φ := continuous_id.add hL
  have hdL (y : ℝ) (hy : 0 < y) : HasDerivAt L (L' y) y :=
    (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul s
  have hdφ (y : ℝ) (hy : 0 < y) : HasDerivAt φ (1 + L' y) y :=
    (hasDerivAt_id y).add (hdL y hy)
  have hLp : ContinuousOn L' (Icc x (x + M)) := by
    apply continuousOn_const.mul
      (continuousOn_const.mul (continuousOn_id.rpow_const ?_))
    intro y hy
    exact Or.inl (ne_of_gt (hx.trans_le hy.1))
  have hLp0 (y : ℝ) (hy : 0 < y) : 0 ≤ L' y := by
    dsimp [L']; positivity
  have hi (f : ℝ → ℝ) (hf : Continuous f) (c d : ℝ) :
      IntervalIntegrable (fun y => E (f y)) volume c d := by
    have h := (increment_comp_integrableOn hE (K := uIcc c d)
      isCompact_uIcc hf (continuous_const (y := (0 : ℝ)))).add
      (integrableOn_const (μ := volume) (C := E 0) isCompact_uIcc.measure_lt_top.ne)
    convert h.intervalIntegrable using 1
    ext y
    simp only [Pi.add_apply, increment, zero_add, sub_add_cancel]
  have hiE (c d : ℝ) : IntervalIntegrable E volume c d := by
    simpa using hi id continuous_id c d
  have hif : IntervalIntegrable (fun r => E (φ (x + r))) volume 0 M :=
    hi (fun r => φ (x + r)) (hφ.comp (continuous_const.add continuous_id)) 0 M
  have hig : IntervalIntegrable (fun r => E (x + r)) volume 0 M :=
    hi _ (continuous_const.add continuous_id) 0 M
  have hiLp : IntervalIntegrable (fun r => L' (x + r)) volume 0 M := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hM.le]
    exact hLp.comp (continuous_const.add continuous_id).continuousOn
      (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hiCorr : IntervalIntegrable
      (fun r => L' (x + r) * E (φ (x + r))) volume 0 M := by
    apply hif.continuousOn_mul
    rw [uIcc_of_le hM.le]
    exact hLp.comp (continuous_const.add continuous_id).continuousOn
      (fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hsubst : (∫ r in (0 : ℝ)..M, E (φ (x + r)) * (1 + L' (x + r))) =
      ∫ y in P..Q, E y := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := M)
      (f := fun r => φ (x + r)) (f' := fun r => 1 + L' (x + r)) (g := E)
      (hφ.comp (continuous_const.add continuous_id)).continuousOn
      (fun r hr => by
        have hr0 : 0 < x + r := by
          have hrpos : 0 < r := by simpa only [min_eq_left hM.le] using hr.1
          linarith
        simpa only [Function.comp_def, mul_one] using
          (hdφ (x + r) hr0).comp r ((hasDerivAt_id r).const_add x))
      (fun r hr => by
        have hr0 : 0 < x + r := by
          have hrpos : 0 < r := by simpa only [min_eq_left hM.le] using hr.1
          linarith
        linarith [hLp0 (x + r) hr0])
    simpa [φ, movingShift, P, Q, L] using h
  have hdelta : (∫ r in (0 : ℝ)..M, L' (x + r)) = δ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r => L (x + r)) (f' := fun r => L' (x + r))
      (fun r hr => by
        rw [uIcc_of_le hM.le] at hr
        have hr0 : 0 < x + r := by linarith [hr.1]
        simpa only [Function.comp_def, mul_one] using
          (hdL (x + r) hr0).comp r ((hasDerivAt_id r).const_add x)) hiLp
    simpa [δ] using h
  have hfirst : (∫ r in (0 : ℝ)..L x, increment E M (x + r)) =
      (∫ y in (x + M)..Q₀, E y) - ∫ y in x..P, E y := by
    simp only [increment]
    rw [intervalIntegral.integral_sub
      (hi _ (by fun_prop) _ _) (hi _ (by fun_prop) _ _)]
    have ht (c : ℝ) : (∫ r in (0 : ℝ)..L x, E (c + r)) =
        ∫ y in c..(c + L x), E y := by
      simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := L x) E c
    rw [show (fun r => E (x + r + M)) = (fun r => E ((x + M) + r)) by
      funext r; congr 1; ring, ht (x + M), ht x]
  have hlast : (∫ v in (0 : ℝ)..δ, E (Q₀ + v) - E x) =
      (∫ y in Q₀..Q, E y) - δ * E x := by
    rw [intervalIntegral.integral_sub (hi _ (by fun_prop) _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    have ht := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) E Q₀
    simp only [add_zero] at ht
    rw [ht, show Q₀ + δ = Q by dsimp [Q₀, δ, Q]; ring]
    simp
  have hcorr : (∫ r in (0 : ℝ)..M, L' (x + r) * (E (φ (x + r)) - E x)) =
      (∫ r in (0 : ℝ)..M, L' (x + r) * E (φ (x + r))) - δ * E x := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiCorr (hiLp.mul_const _),
      intervalIntegral.integral_mul_const, hdelta]
  have hmain : M * windowAverage M (movingIncrement E a s) x =
      (∫ y in P..Q, E y) -
      (∫ r in (0 : ℝ)..M, L' (x + r) * E (φ (x + r))) -
      ∫ y in x..(x + M), E y := by
    have he : (fun r => E (φ (x + r)) * (1 + L' (x + r))) =
        (fun r => E (φ (x + r)) + L' (x + r) * E (φ (x + r))) := by
      funext r; ring
    rw [he, intervalIntegral.integral_add hif hiCorr] at hsubst
    unfold windowAverage
    rw [mul_div_cancel₀ _ hM.ne']
    change (∫ r in (0 : ℝ)..M, E (φ (x + r)) - E (x + r)) = _
    rw [intervalIntegral.integral_sub hif hig]
    have ht := intervalIntegral.integral_comp_add_left (a := 0) (b := M) E x
    simp only [add_zero] at ht
    rw [ht]
    linarith
  change M * windowAverage M (movingIncrement E a s) x =
    (∫ r in (0 : ℝ)..L x, increment E M (x + r)) -
    (∫ r in (0 : ℝ)..M, L' (x + r) * (E (φ (x + r)) - E x)) +
    ∫ v in (0 : ℝ)..δ, E (Q₀ + v) - E x
  rw [hmain, hfirst, hcorr, hlast]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hiE x P) (hiE P Q)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hiE x (x + M))
    (hiE (x + M) Q₀)
  have h3 := intervalIntegral.integral_add_adjacent_intervals (hiE x Q₀) (hiE Q₀ Q)
  linarith

end
end D5.S3.Arith.Robin.ForwardKernel.MovingAverageIdentity
