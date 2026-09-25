/- GID: D5/S3/Analytic/Curvature/CardinalSplineRecurrence
   generality: G
   mirror-B: D5/B/S3/Analytic/Curvature/CardinalSplineRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ContDiff.Deriv, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus]
   utility: none
   digest: Normalized cardinal splines satisfy their knot-safe derivative, Pascal recurrence, box average, and moving-window identities. -/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-
The positive-part lemma below is ported from physlib commit
50ac243729e00925f91224e3916cce74bb971edf,
PhyslibAlpha/ClassicalMechanics/NortonDome/PosPartPow.lean.
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0; full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Upstream authors: Zhi Kai Pong.
Modifications: namespace, imports, and adaptation from Lean 4.34.0/mathlib
5ed2965256430c3649e86755f9576b54eca72435 to this repository's pinned toolchain.
The pinned upstream tree has no NOTICE file.
Retirement: delete this local lemma and directly apply the equivalent declaration when a
Mathlib revision pinned by this repository supplies them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Curvature.CardinalSplineRecurrence

open Filter Topology Set intervalIntegral
open scoped BigOperators

private lemma hasDerivAt_max_sub_pow (c : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => max (y - c) 0 ^ (n + 2))
      (((n : ℝ) + 2) * max (x - c) 0 ^ (n + 1)) x := by
  rcases lt_trichotomy x c with hx | rfl | hx
  · have hev : (fun y : ℝ => max (y - c) 0 ^ (n + 2)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [max_eq_right (sub_nonpos.mpr (Set.mem_Iio.mp hy).le)]
    rw [max_eq_right (sub_nonpos.mpr hx.le), zero_pow (Nat.succ_ne_zero _), mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [sub_self, max_self, zero_pow (Nat.succ_ne_zero _), mul_zero,
      hasDerivAt_iff_tendsto_slope_zero]
    have h : ∀ t : ℝ, t ≠ 0 →
        max t 0 ^ (n + 1) = t⁻¹ • (max (x + t - x) 0 ^ (n + 2) - max (x - x) 0 ^ (n + 2)) := by
      intro t ht
      rw [add_sub_cancel_left, sub_self, max_self, zero_pow (Nat.succ_ne_zero _), sub_zero,
        smul_eq_mul]
      rcases le_or_gt t 0 with h | h
      · simp [max_eq_right h]
      · rw [max_eq_left h.le]
        field_simp
        ring
    have hcont : Continuous (fun t : ℝ => max t 0 ^ (n + 1)) := by fun_prop
    have hc : Tendsto (fun t : ℝ => max t 0 ^ (n + 1)) (𝓝[≠] 0) (𝓝 0) := by
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hc.congr' (eventually_nhdsWithin_of_forall fun t ht => h t ht)
  · have hev : (fun y : ℝ => max (y - c) 0 ^ (n + 2)) =ᶠ[𝓝 x]
        fun y => (y - c) ^ (n + 2) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [max_eq_left (sub_nonneg.mpr (Set.mem_Ioi.mp hy).le)]
    rw [max_eq_left (sub_nonneg.mpr hx.le)]
    have h1 : HasDerivAt (fun y : ℝ => y - c) 1 x := (hasDerivAt_id x).sub_const c
    refine ((HasDerivAt.pow h1 (n + 2)).congr_of_eventuallyEq hev).congr_deriv ?_
    change ((n + 2 : ℕ) : ℝ) * (x - c) ^ (n + 1) * 1 = _
    push_cast
    ring

/-- A normalized finite positive-part polynomial. This is the single spline representation. -/
def T (m q : ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ k * (m.choose k : ℝ) * max (x - k) 0 ^ q) / q.factorial

/-- The first spline derivative, represented without invoking `deriv`. -/
def D (m : ℕ) : ℝ → ℝ := T m (m - 2)

/-- The second spline derivative, represented without invoking `deriv`. -/
def C (m : ℕ) : ℝ → ℝ := T m (m - 3)

/-- The off-center point used by the strict-sign argument. -/
def s (m : ℕ) : ℝ := (m : ℝ) / 2 - 2 / 3

/-- The global reflected first-derivative difference. -/
def Q (m : ℕ) (u : ℝ) : ℝ := D m (s m - u) - D m (s m + u)

/-- Differentiation across every knot lowers the normalized exponent by one. -/
theorem T_hasDerivAt (m q : ℕ) (hq : 1 ≤ q) (x : ℝ) :
    HasDerivAt (T m (q + 1)) (T m q x) x := by
  unfold T
  have hsummand (k : ℕ) :
      HasDerivAt
        (fun y : ℝ => (-1 : ℝ) ^ k * (m.choose k : ℝ) * max (y - k) 0 ^ (q + 1))
        (((q + 1 : ℕ) : ℝ) *
          ((-1 : ℝ) ^ k * (m.choose k : ℝ) * max (x - k) 0 ^ q)) x := by
    let n := q - 1
    have hqn : q = n + 1 := by omega
    rw [hqn]
    have hpow : n + 1 + 1 = n + 2 := by omega
    have hcoef : (((n + 1 + 1 : ℕ) : ℝ)) = (n : ℝ) + 2 := by
      push_cast
      ring
    simpa only [hpow, hcoef, mul_assoc, mul_left_comm, mul_comm]
      using HasDerivAt.const_mul ((-1 : ℝ) ^ k * (m.choose k : ℝ))
        (hasDerivAt_max_sub_pow (k : ℝ) n x)
  have hsum := (HasDerivAt.fun_sum fun k (_hk : k ∈ Finset.range (m + 1)) => hsummand k)
  have hdiv := hsum.div_const (((q + 1).factorial : ℕ) : ℝ)
  apply hdiv.congr_deriv
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    ← Finset.mul_sum]
  field_simp [Nat.factorial_ne_zero]

/-- Raising the order averages `D` over the preceding unit interval. -/
theorem D_succ_eq_integral (m : ℕ) (hm : 3 ≤ m) (x : ℝ) :
    D (m + 1) x = ∫ t in x - 1..x, D m t := by
  have hq : 1 ≤ m - 2 := by omega
  have hder (t : ℝ) : HasDerivAt (T m (m - 1)) (D m t) t := by
    unfold D
    simpa only [show m - 2 + 1 = m - 1 by omega] using
      T_hasDerivAt m (m - 2) hq t
  have hint : IntervalIntegrable (D m) MeasureTheory.volume (x - 1) x := by
    have hcont : Continuous (D m) := by
      unfold D T
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hpascal : T (m + 1) (m - 1) x = T m (m - 1) x - T m (m - 1) (x - 1) := by
    unfold T
    have hsum :
        (∑ i ∈ Finset.range (m + 2), (-1 : ℝ) ^ i * (m + 1).choose i *
            max (x - i) 0 ^ (m - 1)) =
          (∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * m.choose i *
            max (x - i) 0 ^ (m - 1)) -
          ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * m.choose i *
            max (x - ((i + 1 : ℕ) : ℝ)) 0 ^ (m - 1) := by
      have h := Finset.sum_choose_succ_mul (R := ℝ)
        (fun i _ => (-1 : ℝ) ^ i * max (x - i) 0 ^ (m - 1)) m
      simp only [pow_succ] at h
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      ring_nf at h ⊢
      exact h
    rw [hsum, sub_div]
    congr 1
    apply congrArg (fun z : ℝ => z / ((m - 1).factorial : ℝ))
    apply Finset.sum_congr rfl
    intro i _hi
    congr 3
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ht => hder t) hint]
  simpa only [D, show m + 1 - 2 = m - 1 by omega] using hpascal

/-- The reflected difference inherits an exact centered moving-window average. -/
theorem Q_succ_eq_integral (m : ℕ) (hm : 3 ≤ m) (u : ℝ) :
    Q (m + 1) u = ∫ t in u - 1 / 2..u + 1 / 2, Q m t := by
  let a : ℝ := u - 1 / 2
  let b : ℝ := u + 1 / 2
  have hs : s (m + 1) = s m + 1 / 2 := by
    unfold s
    push_cast
    ring
  have hD : Continuous (D m) := by
    unfold D T
    fun_prop
  have hminus : IntervalIntegrable (fun t : ℝ => D m (s m - t))
      MeasureTheory.volume a b := by
    exact (hD.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hplus : IntervalIntegrable (fun t : ℝ => D m (s m + t))
      MeasureTheory.volume a b := by
    exact (hD.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hplus_change :
      (∫ t in a..b, D m (s m + t)) = ∫ t in s m + a..s m + b, D m t := by
    simpa only [add_comm] using
      (intervalIntegral.integral_comp_add_right (f := D m) (a := a) (b := b) (s m))
  unfold Q
  rw [D_succ_eq_integral m hm, D_succ_eq_integral m hm,
    intervalIntegral.integral_sub hminus hplus,
    intervalIntegral.integral_comp_sub_left, hplus_change, hs]
  dsimp only [a, b]
  congr 1 <;> ring

end D5.S3.Analytic.Curvature.CardinalSplineRecurrence
