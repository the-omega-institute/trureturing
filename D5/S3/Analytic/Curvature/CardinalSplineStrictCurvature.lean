/- GID: D5/S3/Analytic/Curvature/CardinalSplineStrictCurvature
   generality: G
   mirror-B: D5/B/S3/Analytic/Curvature/CardinalSplineStrictCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Cardinal-spline curvature is strictly negative on the shifted closed core in every order at least five. -/

import D5.S3.Analytic.Curvature.CardinalSplineRecurrence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Curvature.CardinalSplineStrictCurvature

open Set intervalIntegral
open D5.S3.Analytic.Curvature.CardinalSplineRecurrence
open scoped BigOperators Interval

private lemma C_four_neg_on_core_interior {x : ℝ}
    (hx : x ∈ Ioo (s 4) ((4 : ℝ) - s 4)) : C 4 x < 0 := by
  norm_num [s] at hx
  by_cases h2 : x ≤ 2
  · norm_num [C, T, Finset.sum_range_succ, Nat.choose]
    rw [max_eq_left (by linarith : 0 ≤ x), max_eq_left (by linarith : 0 ≤ x - 1)]
    repeat' rw [max_eq_right (by linarith)]
    ring_nf
    linarith
  · norm_num [C, T, Finset.sum_range_succ, Nat.choose]
    rw [max_eq_left (by linarith : 0 ≤ x), max_eq_left (by linarith : 0 ≤ x - 1),
      max_eq_left (by linarith : 0 ≤ x - 2)]
    repeat' rw [max_eq_right (by linarith)]
    ring_nf
    linarith

private theorem D_four_strictAntiOn_core :
    StrictAntiOn (D 4) (Icc (s 4) ((4 : ℝ) - s 4)) := by
  have hcont : Continuous (D 4) := by
    unfold D T
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn
  intro x hx
  have hder : HasDerivAt (D 4) (C 4 x) x := by
    unfold D C
    simpa only [show 4 - 3 + 1 = 4 - 2 by omega] using T_hasDerivAt 4 (4 - 3) (by omega) x
  rw [hder.deriv]
  rw [interior_Icc] at hx
  exact C_four_neg_on_core_interior hx

private structure SplineInvariant (m : ℕ) : Prop where
  support : ∀ x : ℝ, x ≤ 0 ∨ (m : ℝ) ≤ x → D m x = 0
  reflection : ∀ x : ℝ, D m ((m : ℝ) - x) = -D m x
  q_nonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ Q m u
  q_half_pos : 0 < Q m (1 / 2)
  strict_core : StrictAntiOn (D m) (Icc (s m) ((m : ℝ) - s m))

private lemma invariant_support_succ (m : ℕ) (hm : 3 ≤ m) (h : SplineInvariant m)
    (x : ℝ) (hx : x ≤ 0 ∨ ((m + 1 : ℕ) : ℝ) ≤ x) : D (m + 1) x = 0 := by
  rw [D_succ_eq_integral m hm x]
  calc
    (∫ t in x - 1..x, D m t) = ∫ _t in x - 1..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : x - 1 ≤ x)] at ht
      apply h.support t
      rcases hx with hx | hx
      · exact Or.inl (ht.2.trans hx)
      · right
        push_cast at hx
        linarith [ht.1]
    _ = 0 := by simp

private lemma invariant_reflection_succ (m : ℕ) (hm : 3 ≤ m) (h : SplineInvariant m)
    (x : ℝ) : D (m + 1) (((m + 1 : ℕ) : ℝ) - x) = -D (m + 1) x := by
  rw [D_succ_eq_integral m hm, D_succ_eq_integral m hm]
  have hchange :
      (∫ t in x - 1..x, D m ((m : ℝ) - t)) =
        ∫ t in (m : ℝ) - x..(m : ℝ) - (x - 1), D m t := by
    exact intervalIntegral.integral_comp_sub_left (D m) (m : ℝ)
  calc
    (∫ t in ((m + 1 : ℕ) : ℝ) - x - 1..((m + 1 : ℕ) : ℝ) - x, D m t) =
        ∫ t in (m : ℝ) - x..(m : ℝ) - (x - 1), D m t := by
          congr 1 <;> push_cast <;> ring
    _ = ∫ t in x - 1..x, D m ((m : ℝ) - t) := hchange.symm
    _ = ∫ t in x - 1..x, -D m t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      exact h.reflection t
    _ = -(∫ t in x - 1..x, D m t) := by rw [intervalIntegral.integral_neg]

private lemma invariant_q_nonneg_succ (m : ℕ) (hm : 3 ≤ m) (h : SplineInvariant m)
    (u : ℝ) (hu : 0 ≤ u) : 0 ≤ Q (m + 1) u := by
  rw [Q_succ_eq_integral m hm u]
  by_cases hhalf : 1 / 2 ≤ u
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact h.q_nonneg t (by linarith [ht.1])
  · let a : ℝ := 1 / 2 - u
    let b : ℝ := 1 / 2 + u
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hab : a ≤ b := by dsimp [a, b]; linarith
    have hcont : Continuous (Q m) := by
      unfold Q
      have hD : Continuous (D m) := by
        unfold D T
        fun_prop
      exact (hD.comp (continuous_const.sub continuous_id)).sub
        (hD.comp (continuous_const.add continuous_id))
    have hleft : IntervalIntegrable (Q m) MeasureTheory.volume (-a) a :=
      hcont.intervalIntegrable _ _
    have hright : IntervalIntegrable (Q m) MeasureTheory.volume a b :=
      hcont.intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    have hzero : (∫ t in -a..a, Q m t) = 0 := by
      have hodd (t : ℝ) : Q m (-t) = -Q m t := by
        unfold Q
        ring
      have hchange : (∫ t in -a..a, Q m (-t)) = ∫ t in -a..a, Q m t := by
        simpa only [neg_neg] using
          (intervalIntegral.integral_comp_neg (f := Q m) (a := -a) (b := a))
      have hodd : (∫ t in -a..a, Q m (-t)) = -(∫ t in -a..a, Q m t) := by
        calc
          (∫ t in -a..a, Q m (-t)) = ∫ t in -a..a, -Q m t := by
            apply intervalIntegral.integral_congr
            intro t _ht
            exact hodd t
          _ = -(∫ t in -a..a, Q m t) := by rw [intervalIntegral.integral_neg]
      linarith
    have hreduce : (∫ t in -a..b, Q m t) = ∫ t in a..b, Q m t := by
      rw [← hadd, hzero, zero_add]
    have hnonneg : 0 ≤ ∫ t in a..b, Q m t := by
      apply intervalIntegral.integral_nonneg hab
      intro t ht
      exact h.q_nonneg t (ha.trans ht.1)
    rw [show u - 1 / 2 = -a by dsimp [a]; ring,
      show u + 1 / 2 = b by dsimp [b]; ring, hreduce]
    exact hnonneg

private lemma invariant_q_half_pos_succ (m : ℕ) (hm : 3 ≤ m) (h : SplineInvariant m) :
    0 < Q (m + 1) (1 / 2) := by
  rw [Q_succ_eq_integral m hm]
  norm_num
  apply intervalIntegral.integral_pos (by norm_num)
  · have hcont : Continuous (Q m) := by
      unfold Q
      have hD : Continuous (D m) := by
        unfold D T
        fun_prop
      exact (hD.comp (continuous_const.sub continuous_id)).sub
        (hD.comp (continuous_const.add continuous_id))
    exact hcont.continuousOn
  · intro t ht
    exact h.q_nonneg t ht.1.le
  · exact ⟨1 / 2, by norm_num, h.q_half_pos⟩

private lemma C_succ_neg_core (m : ℕ) (hm : 4 ≤ m) (h : SplineInvariant m)
    {x : ℝ} (hx : x ∈ Icc (s (m + 1)) (((m + 1 : ℕ) : ℝ) - s (m + 1))) :
    C (m + 1) x < 0 := by
  have hC (z : ℝ) : C (m + 1) z = D m z - D m (z - 1) := by
    unfold C D
    simp only [show m + 1 - 3 = m - 2 by omega]
    unfold T
    have hsum :
        (∑ i ∈ Finset.range (m + 2), (-1 : ℝ) ^ i * (m + 1).choose i *
            max (z - i) 0 ^ (m - 2)) =
          (∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * m.choose i *
            max (z - i) 0 ^ (m - 2)) -
          ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i * m.choose i *
            max (z - ((i + 1 : ℕ) : ℝ)) 0 ^ (m - 2) := by
      have hpascal := Finset.sum_choose_succ_mul (R := ℝ)
        (fun i _ => (-1 : ℝ) ^ i * max (z - i) 0 ^ (m - 2)) m
      simp only [pow_succ] at hpascal
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      ring_nf at hpascal ⊢
      exact hpascal
    rw [hsum, sub_div]
    congr 1
    apply congrArg (fun w : ℝ => w / ((m - 2).factorial : ℝ))
    apply Finset.sum_congr rfl
    intro i _hi
    congr 3
    push_cast
    ring
  have hleft {z : ℝ} (hz : z ∈ Icc (s (m + 1)) (((m + 1 : ℕ) : ℝ) / 2)) :
      C (m + 1) z < 0 := by
    let t := z - s m
    have hs : s (m + 1) = s m + 1 / 2 := by
      unfold s
      push_cast
      ring
    have hzform : z = s m + t := by dsimp [t]; ring
    have ht0 : 1 / 2 ≤ t := by
      rw [hs] at hz
      dsimp [t]
      linarith [hz.1]
    have ht1 : t ≤ 7 / 6 := by
      dsimp [t, s] at *
      push_cast at hz
      linarith [hz.2]
    rw [hC, hzform]
    by_cases heq : t = 1 / 2
    · have hhalf := h.q_half_pos
      unfold Q at hhalf
      apply sub_neg.mpr
      have hp := sub_pos.mp hhalf
      rw [heq]
      convert hp using 1
      · ring
    by_cases hlt : t < 1
    · have htpos : 0 < 1 - t := by linarith
      have hthalf : 1 / 2 < t := lt_of_le_of_ne ht0 (Ne.symm heq)
      have hq := h.q_nonneg (1 - t) htpos.le
      unfold Q at hq
      have ha : s m + (1 - t) ∈ Icc (s m) ((m : ℝ) - s m) := by
        constructor
        · linarith
        · unfold s
          linarith
      have hb : s m + t ∈ Icc (s m) ((m : ℝ) - s m) := by
        constructor
        · linarith
        · unfold s
          linarith
      have hstrict := h.strict_core ha hb (by linarith : s m + (1 - t) < s m + t)
      have hq' : D m (s m + (1 - t)) ≤ D m (s m + t - 1) := by
        have hq' := sub_nonneg.mp hq
        convert hq' using 1
        · ring
      exact sub_neg.mpr (hstrict.trans_le hq')
    · have ha : s m + t - 1 ∈ Icc (s m) ((m : ℝ) - s m) := by
        constructor
        · linarith
        · unfold s
          linarith
      have hb : s m + t ∈ Icc (s m) ((m : ℝ) - s m) := by
        constructor
        · linarith
        · unfold s
          linarith
      exact sub_neg.mpr (h.strict_core ha hb (by linarith))
  by_cases hmid : x ≤ ((m + 1 : ℕ) : ℝ) / 2
  · exact hleft ⟨hx.1, hmid⟩
  · let y := ((m + 1 : ℕ) : ℝ) - x
    have hy : y ∈ Icc (s (m + 1)) (((m + 1 : ℕ) : ℝ) / 2) := by
      constructor
      · dsimp [y]
        linarith [hx.2]
      · dsimp [y]
        linarith
    have hreflect (z : ℝ) : C (m + 1) (((m + 1 : ℕ) : ℝ) - z) = C (m + 1) z := by
      rw [hC, hC]
      rw [show ((m + 1 : ℕ) : ℝ) - z = (m : ℝ) - (z - 1) by push_cast; ring,
        show (m : ℝ) - (z - 1) - 1 = (m : ℝ) - z by ring]
      rw [h.reflection (z - 1), h.reflection z]
      ring
    rw [← hreflect x]
    exact hleft hy

private lemma invariant_of_four_le (m : ℕ) (hm : 4 ≤ m) : SplineInvariant m := by
  induction m, hm using Nat.le_induction with
  | base =>
      have hD_nonpos {x : ℝ} (hx : x ≤ 0) : D 4 x = 0 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        repeat' rw [max_eq_right (by linarith)]
        norm_num
      have hD01 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : D 4 x = x ^ 2 / 2 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        rw [max_eq_left hx0]
        repeat' rw [max_eq_right (by linarith)]
        ring
      have hD12 {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
          D 4 x = x ^ 2 / 2 - 2 * (x - 1) ^ 2 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        rw [max_eq_left (by linarith : 0 ≤ x), max_eq_left (by linarith : 0 ≤ x - 1)]
        repeat' rw [max_eq_right (by linarith)]
        ring
      have hD23 {x : ℝ} (hx2 : 2 ≤ x) (hx3 : x ≤ 3) :
          D 4 x = x ^ 2 / 2 - 2 * (x - 1) ^ 2 + 3 * (x - 2) ^ 2 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        rw [max_eq_left (by linarith : 0 ≤ x), max_eq_left (by linarith : 0 ≤ x - 1),
          max_eq_left (by linarith : 0 ≤ x - 2)]
        repeat' rw [max_eq_right (by linarith)]
        ring
      have hD34 {x : ℝ} (hx3 : 3 ≤ x) (hx4 : x ≤ 4) :
          D 4 x = x ^ 2 / 2 - 2 * (x - 1) ^ 2 + 3 * (x - 2) ^ 2 -
            2 * (x - 3) ^ 2 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        rw [max_eq_left (by linarith : 0 ≤ x), max_eq_left (by linarith : 0 ≤ x - 1),
          max_eq_left (by linarith : 0 ≤ x - 2), max_eq_left (by linarith : 0 ≤ x - 3)]
        rw [max_eq_right (by linarith : x - 4 ≤ 0)]
        ring
      have hD_ge4 {x : ℝ} (hx : 4 ≤ x) : D 4 x = 0 := by
        norm_num [D, T, Finset.sum_range_succ, Nat.choose]
        repeat' rw [max_eq_left (by linarith)]
        ring
      refine {
        support := ?_, reflection := ?_, q_nonneg := ?_, q_half_pos := ?_,
        strict_core := D_four_strictAntiOn_core }
      · intro x hx
        rcases hx with hx | hx
        · exact hD_nonpos hx
        · exact hD_ge4 hx
      · intro x
        norm_num
        by_cases h0 : x ≤ 0
        · rw [hD_nonpos h0, hD_ge4 (by linarith)]
          simp
        by_cases h1 : x ≤ 1
        · rw [hD01 (by linarith) h1,
            hD34 (x := 4 - x) (by linarith) (by linarith)]
          ring
        by_cases h2 : x ≤ 2
        · rw [hD12 (by linarith) h2,
            hD23 (x := 4 - x) (by linarith) (by linarith)]
          ring
        by_cases h3 : x ≤ 3
        · rw [hD23 (by linarith) h3,
            hD12 (x := 4 - x) (by linarith) (by linarith)]
          ring
        by_cases h4 : x ≤ 4
        · rw [hD34 (by linarith) h4,
            hD01 (x := 4 - x) (by linarith) (by linarith)]
          ring
        · rw [hD_ge4 (x := x) (by linarith),
            hD_nonpos (x := 4 - x) (by linarith)]
          simp
      · intro u hu
        unfold Q
        norm_num [s]
        by_cases h1 : u ≤ 1 / 3
        · rw [hD12 (x := 4 / 3 - u) (by linarith) (by linarith),
            hD12 (x := 4 / 3 + u) (by linarith) (by linarith)]
          ring_nf
          exact le_rfl
        by_cases h2 : u ≤ 2 / 3
        · rw [hD01 (x := 4 / 3 - u) (by linarith) (by linarith),
            hD12 (x := 4 / 3 + u) (by linarith) (by linarith)]
          nlinarith [sq_nonneg (3 * u - 1)]
        by_cases h3 : u ≤ 4 / 3
        · rw [hD01 (x := 4 / 3 - u) (by linarith) (by linarith),
            hD23 (x := 4 / 3 + u) (by linarith) (by linarith)]
          have hp : (u - 2 / 3) * (u - 4 / 3) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          nlinarith
        by_cases h4 : u ≤ 5 / 3
        · rw [hD_nonpos (x := 4 / 3 - u) (by linarith),
            hD23 (x := 4 / 3 + u) (by linarith) (by linarith)]
          have hp : 0 ≤ (2 - u) * (3 * u - 2) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
        by_cases h5 : u ≤ 8 / 3
        · rw [hD_nonpos (x := 4 / 3 - u) (by linarith),
            hD34 (x := 4 / 3 + u) (by linarith) (by linarith)]
          nlinarith [sq_nonneg (3 * u - 8)]
        · rw [hD_nonpos (x := 4 / 3 - u) (by linarith),
            hD_ge4 (x := 4 / 3 + u) (by linarith)]
      · norm_num [Q, s, D, T, Finset.sum_range_succ, Nat.choose, max_def]
  | succ m hm ih =>
      have hstrict : StrictAntiOn (D (m + 1))
          (Icc (s (m + 1)) (((m + 1 : ℕ) : ℝ) - s (m + 1))) := by
        have hcont : Continuous (D (m + 1)) := by
          unfold D T
          fun_prop
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn
        intro x hx
        rw [interior_Icc] at hx
        have hder : HasDerivAt (D (m + 1)) (C (m + 1) x) x := by
          unfold D C
          simpa only [show m + 1 - 3 + 1 = m + 1 - 2 by omega] using
            T_hasDerivAt (m + 1) (m + 1 - 3) (by omega) x
        rw [hder.deriv]
        exact C_succ_neg_core m hm ih ⟨hx.1.le, hx.2.le⟩
      exact {
        support := invariant_support_succ m (by omega) ih,
        reflection := invariant_reflection_succ m (by omega) ih,
        q_nonneg := invariant_q_nonneg_succ m (by omega) ih,
        q_half_pos := invariant_q_half_pos_succ m (by omega) ih,
        strict_core := hstrict }

/-- The second derivative of the normalized cardinal spline is strictly negative on
its closed central core. The order-four base is excluded because its two core endpoint
values are zero. -/
theorem cardinalSpline_strict_curvature (m : ℕ) (hm : 5 ≤ m) {x : ℝ}
    (hx : x ∈ Icc (s m) ((m : ℝ) - s m)) : C m x < 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact C_succ_neg_core k (by omega) (invariant_of_four_le k (by omega)) hx

end D5.S3.Analytic.Curvature.CardinalSplineStrictCurvature
