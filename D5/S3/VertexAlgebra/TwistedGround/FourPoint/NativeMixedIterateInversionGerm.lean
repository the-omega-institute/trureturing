/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateInversionGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedIterateInversionGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summed detector inversion for the native mixed Leech A iterate. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedIterateInversionCoefficient
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Detector inversion of the native mixed A series on the normalized ratio disk,
given convergence of the exchanged descendant series. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (Twisted leechUnit)
open Orbifold.NativeOddUpperRightSkew (lowering mixedPairing_lowering_tail)
open Orbifold.NativeMixedPairSkew (swapInput)
open Orbifold.NativeMixedIterateInversionCoefficient (aCoeff aCoeff_inversion)

local notation "ℒ" => leechData
local notation "T" => lowering ℒ leechUnit
private abbrev State (s : Bool) := Twisted ℒ leechUnit s
private abbrev weight (M : ℕ) : ℤ := 3 + (M : ℤ)
private abbrev factorials (i j : ℕ) : ℂ := (i.factorial : ℂ) * (j.factorial : ℂ)

/-- The exponent of the principal binomial in the exchanged iterate. -/
def binomialExponent (mP mQ mR mS : ℤ) (j : ℕ) : ℂ :=
  ((mS : ℂ) - (mR : ℂ) - (mP : ℂ) + (mQ : ℂ)) / 2 - (j : ℂ)

private theorem one_add_re_pos {ρ : ℂ} (hρ : ‖ρ‖ < 1) : 0 < (1 + ρ).re := by
  have hre := (abs_le.mp (Complex.abs_re_le_norm ρ)).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

private theorem one_add_slit {ρ : ℂ} (hρ : ‖ρ‖ < 1) : 1 + ρ ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (one_add_re_pos hρ))

/-- The branch of the binomial power continued from zero on the entire ratio disk. -/
theorem principal_binomial_germ (β : ℂ) :
    AnalyticOnNhd ℂ (fun ρ : ℂ => (1 + ρ) ^ β) (Metric.ball 0 1) ∧
    Set.EqOn (fun ρ : ℂ => (1 + ρ) ^ β)
      (fun ρ : ℂ => Complex.exp (Complex.log (1 + ρ) * β)) (Metric.ball 0 1) ∧
    (1 + (0 : ℂ)) ^ β = 1 ∧
    HasFPowerSeriesOnBall (fun ρ : ℂ => (1 + ρ) ^ β) (binomialSeries ℂ β) 0 1 := by
  refine ⟨?_, ?_, by simp, Complex.one_add_cpow_hasFPowerSeriesOnBall_zero⟩
  · intro ρ hρ
    have ha : AnalyticAt ℂ (fun z : ℂ => 1 + z) ρ :=
      analyticAt_const.add analyticAt_id
    exact ha.cpow analyticAt_const (one_add_slit (mem_ball_zero_iff.mp hρ))
  · intro ρ hρ
    exact Complex.cpow_def_of_ne_zero
      (Complex.slitPlane_ne_zero (one_add_slit (mem_ball_zero_iff.mp hρ))) β

private theorem hasSum_binomial (β : ℂ) {ρ : ℂ} (hρ : ‖ρ‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose β n * ρ ^ n) ((1 + ρ) ^ β) := by
  have hb : ρ ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    exact mem_ball_zero_iff.mpr hρ
  have hs := (principal_binomial_germ β).2.2.2.hasSum_sub hb
  simpa only [sub_zero, binomialSeries_apply, List.ofFn_const, List.prod_replicate,
    smul_eq_mul] using hs

private def shiftedBinomial (β : ℂ) (a : ℕ → ℂ) (d n : ℕ) : ℂ :=
  if d ≤ n then
    ∑ l ∈ Finset.range (n - d + 1), Ring.choose β l * a (n - d - l)
  else 0

set_option maxHeartbeats 1200000 in
-- Elaborating the norm-summable product and its shifted finite sums takes extra heartbeats.
private theorem hasSum_shiftedBinomial (β : ℂ) (a : ℕ → ℂ) (d : ℕ) {ρ value : ℂ}
    (hρ : ‖ρ‖ < 1) (ha : HasSum (fun n : ℕ => a n * ρ ^ n) value) :
    HasSum (fun n : ℕ => shiftedBinomial β a d n * ρ ^ n)
      (ρ ^ d * ((1 + ρ) ^ β * value)) := by
  let b (n : ℕ) := Ring.choose β n * ρ ^ n
  let c (n : ℕ) := a n * ρ ^ n
  have hb : HasSum b ((1 + ρ) ^ β) := hasSum_binomial β hρ
  have hc : HasSum c value := ha
  have hprod := hasSum_sum_range_mul_of_summable_norm (f := b) (g := c)
    hb.summable.norm hc.summable.norm
  rw [hb.tsum_eq, hc.tsum_eq] at hprod
  let shift (n : ℕ) := n + d
  have hinj : Function.Injective shift := by
    intro n m h
    dsimp only [shift] at h
    omega
  have hoff (n : ℕ) (hn : n ∉ Set.range shift) :
      shiftedBinomial β a d n * ρ ^ n = 0 := by
    have hnd : ¬ d ≤ n := by
      intro h
      apply hn
      exact ⟨n - d, by dsimp [shift]; omega⟩
    simp [shiftedBinomial, hnd]
  apply (hinj.hasSum_iff hoff).mp
  refine (hprod.mul_left (ρ ^ d)).congr_fun fun n => ?_
  change shiftedBinomial β a d (n + d) * ρ ^ (n + d) = _
  rw [shiftedBinomial, ite_eq_left (by omega), Nat.add_sub_cancel, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hln := Finset.mem_range.mp hl
  have hn : l + (n - l) = n := by omega
  dsimp only [b, c]
  have hpow : ρ ^ n = ρ ^ l * ρ ^ (n - l) := by rw [← pow_add, hn]
  rw [pow_add ρ n d, hpow]
  ring

private theorem sum_range_eq_of_zero_tail (f : ℕ → ℂ) (a b : ℕ)
    (ha : ∀ k, a ≤ k → f k = 0) (hb : ∀ k, b ≤ k → f k = 0) :
    (∑ k ∈ Finset.range a, f k) = ∑ k ∈ Finset.range b, f k := by
  calc
    _ = ∑ k ∈ Finset.range (max a b), f k :=
      Finset.sum_subset (Finset.range_mono (le_max_left a b)) fun k _ hk =>
        ha k (Nat.le_of_not_gt fun h => hk (Finset.mem_range.mpr h))
    _ = _ := (Finset.sum_subset (Finset.range_mono (le_max_right a b)) fun k _ hk =>
        hb k (Nat.le_of_not_gt fun h => hk (Finset.mem_range.mpr h))).symm

private abbrev exchangedCoeff (s t : Bool) (mP mQ mR mS : ℤ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (j i : ℕ) : ℕ → ℂ :=
  fun F => aCoeff (!s) (!t) (mQ - 2 * (j : ℤ)) (mP - 2 * (i : ℤ)) mS mR F
    ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P)) S (swapInput R)

private theorem swap_zero (s : Bool) : swapInput (0 : State s) = 0 := by
  cases s <;> rfl

private theorem rectangle_coefficient (s t : Bool) (M K H J N : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J) :
    aCoeff s t (weight M) (weight K) (weight H) (weight J) N P Q R S =
      I ^ (weight M - weight K) *
        ∑ j ∈ Finset.range (K / 2 + 1), ∑ i ∈ Finset.range (M / 2 + 1),
          (factorials i j)⁻¹ *
            shiftedBinomial (binomialExponent (weight M) (weight K) (weight H) (weight J) j)
              (exchangedCoeff s t (weight M) (weight K) (weight H) (weight J) P Q R S j i)
              (j + i) N := by
  let b := exchangedCoeff s t (weight M) (weight K) (weight H) (weight J) P Q R S
  let β := binomialExponent (weight M) (weight K) (weight H) (weight J)
  let g (j i : ℕ) := (factorials i j)⁻¹ * shiftedBinomial (β j) (b j i) (j + i) N
  change _ = _ * ∑ j ∈ Finset.range (K / 2 + 1), ∑ i ∈ Finset.range (M / 2 + 1), g j i
  have hgN (j i : ℕ) (hn : N < j + i) : g j i = 0 := by
    simp [g, shiftedBinomial, Nat.not_le.mpr hn]
  have hgM (j i : ℕ) (hi : M / 2 + 1 ≤ i) : g j i = 0 := by
    have hz := mixedPairing_lowering_tail s M P hP i hi
    have hb (F : ℕ) : b j i F = 0 := by simp [b, aCoeff, hz, swap_zero]
    simp [g, shiftedBinomial, hb]
  have hgK (j i : ℕ) (hj : K / 2 + 1 ≤ j) : g j i = 0 := by
    have hz := mixedPairing_lowering_tail (!s) K Q hQ j hj
    have hb (F : ℕ) : b j i F = 0 := by simp [b, aCoeff, hz]
    simp [g, shiftedBinomial, hb]
  rw [aCoeff_inversion s t M K H J N P Q R S hP hQ hR hS]
  apply congrArg (fun v : ℂ => I ^ (weight M - weight K) * v)
  calc
    _ = ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (N - j + 1), g j i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN := Finset.mem_range.mp hj
      apply Finset.sum_congr rfl
      intro i hi
      have hiN := Finset.mem_range.mp hi
      dsimp only [g]
      rw [shiftedBinomial, ite_eq_left (by omega), show N - (j + i) = N - j - i by omega,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro L _
      change Ring.choose (β j) L / factorials i j * b j i (N - j - i - L) =
        (factorials i j)⁻¹ * (Ring.choose (β j) L * b j i (N - j - i - L))
      rw [div_eq_mul_inv]
      ac_rfl
    _ = ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (M / 2 + 1), g j i := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN := Finset.mem_range.mp hj
      exact sum_range_eq_of_zero_tail (g j) (N - j + 1) (M / 2 + 1)
        (fun i hi => hgN j i (by omega)) (hgM j)
    _ = _ :=
      sum_range_eq_of_zero_tail (fun j => ∑ i ∈ Finset.range (M / 2 + 1), g j i)
        (N + 1) (K / 2 + 1)
        (fun j hj => Finset.sum_eq_zero fun i _ => hgN j i (by omega))
        (fun j hj => Finset.sum_eq_zero fun i _ => hgK j i hj)

/-- The summed inversion of the actual A coefficients on the normalized ratio disk.
Each supplied value is a series of the exchanged native descendants. -/
theorem aCoeff_inversion_hasSum (s t : Bool) (M K H J : ℕ)
    (P : State s) (Q : State (!s)) (R : State t) (S : State (!t))
    (hP : P.val ∈ actualGrade ℒ leechUnit M) (hQ : Q.val ∈ actualGrade ℒ leechUnit K)
    (hR : R.val ∈ actualGrade ℒ leechUnit H) (hS : S.val ∈ actualGrade ℒ leechUnit J)
    {ρ : ℂ} (hρ : ‖ρ‖ < 1) (value : ℕ → ℕ → ℂ)
    (hDesc : ∀ j i : ℕ, j ≤ K / 2 → i ≤ M / 2 →
      HasSum (fun F : ℕ =>
        aCoeff (!s) (!t) (weight K - 2 * (j : ℤ)) (weight M - 2 * (i : ℤ))
          (weight J) (weight H) F ((T (!s) ^ j) Q) (swapInput ((T s ^ i) P)) S (swapInput R) *
            ρ ^ F) (value j i)) :
    HasSum (fun N : ℕ => aCoeff s t (weight M) (weight K) (weight H) (weight J) N P Q R S *
        ρ ^ N)
      (I ^ (weight M - weight K) *
        ∑ j ∈ Finset.range (K / 2 + 1), ∑ i ∈ Finset.range (M / 2 + 1),
          (factorials i j)⁻¹ *
            (ρ ^ (j + i) *
              ((1 + ρ) ^ binomialExponent (weight M) (weight K) (weight H) (weight J) j *
                value j i))) := by
  have hs := (hasSum_sum (s := Finset.range (K / 2 + 1)) fun j hj =>
    hasSum_sum (s := Finset.range (M / 2 + 1)) fun i hi =>
      (hasSum_shiftedBinomial (binomialExponent (weight M) (weight K) (weight H) (weight J) j)
        (exchangedCoeff s t (weight M) (weight K) (weight H) (weight J) P Q R S j i)
        (j + i) hρ
        (hDesc j i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))).mul_left (factorials i j)⁻¹).mul_left
    (I ^ (weight M - weight K))
  refine hs.congr_fun fun N => ?_
  rw [rectangle_coefficient s t M K H J N P Q R S hP hQ hR hS]
  simp only [mul_assoc, Finset.sum_mul]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedIterateInversionGerm
