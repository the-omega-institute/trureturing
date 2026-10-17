import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-
Transient, source-only application of existing Mathlib suppliers.
Target: Lean v4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
This file has not been compiled. It retains no named mathematical declaration.
The premises describe given curves for the original multiplicative field K.
Native curvature/potential identification, occurrence assembly, existence,
continuation, and convergence are outside this example.
-/

open Set Filter
open scoped BigOperators Topology

theorem CFMP164Transient.original_multiplicative_flow_check {I : Type*} [Fintype I]
    (D : Set (I → ℝ)) (K : (I → ℝ) → I → ℝ)
    (x y : ℝ → I → ℝ) (a b C : ℝ)
    (hpositive : ∀ p ∈ D, ∀ i, 0 < p i)
    (hanti : ∀ p ∈ D, ∀ q ∈ D,
      (∑ i, (p i - q i) * (K p i - K q i)) ≤ 0)
    (hupper : ∀ p ∈ D, ∀ i, K p i ≤ C)
    (hxcont : ContinuousOn x (Icc a b))
    (hycont : ContinuousOn y (Icc a b))
    (hxmem : ∀ t ∈ Icc a b, x t ∈ D)
    (hymem : ∀ t ∈ Icc a b, y t ∈ D)
    (hxderiv : ∀ t ∈ Ico a b, ∀ i,
      HasDerivWithinAt (fun r => x r i)
        (x t i * K (x t) i) (Ici t) t)
    (hyderiv : ∀ t ∈ Ico a b, ∀ i,
      HasDerivWithinAt (fun r => y r i)
        (y t i * K (y t) i) (Ici t) t) :
    (∀ t ∈ Icc a b,
      (∑ i, (Real.sqrt (x t i) - Real.sqrt (y t i)) ^ 2) ≤
        Real.exp (C * (t - a)) *
          (∑ i, (Real.sqrt (x a i) - Real.sqrt (y a i)) ^ 2)) ∧
    (x a = y a → EqOn x y (Icc a b)) := by
  classical
  let z : ℝ → I → ℝ := fun t i => Real.sqrt (x t i)
  let w : ℝ → I → ℝ := fun t i => Real.sqrt (y t i)
  let H : ℝ → ℝ := fun t => ∑ i, (z t i - w t i) ^ 2
  let Hprime : ℝ → ℝ := fun t =>
    ∑ i, (z t i - w t i) *
      (z t i * K (x t) i - w t i * K (y t) i)

  have hzsq : ∀ t ∈ Icc a b, ∀ i, (z t i) ^ 2 = x t i := by
    intro t ht i
    exact Real.sq_sqrt (le_of_lt (hpositive (x t) (hxmem t ht) i))
  have hwsq : ∀ t ∈ Icc a b, ∀ i, (w t i) ^ 2 = y t i := by
    intro t ht i
    exact Real.sq_sqrt (le_of_lt (hpositive (y t) (hymem t ht) i))

  have hHnonneg : ∀ t, 0 ≤ H t := by
    intro t
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (z t i - w t i))

  have hHcont : ContinuousOn H (Icc a b) := by
    dsimp only [H]
    refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
    exact (((continuous_apply i).comp_continuousOn hxcont).sqrt.sub
      ((continuous_apply i).comp_continuousOn hycont).sqrt).pow 2

  -- Derive every square-root derivative on the original within set Ici t.
  have hHderiv : ∀ t ∈ Ico a b,
      HasDerivWithinAt H (Hprime t) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    have hcoord : ∀ i,
        HasDerivWithinAt (fun r => (z r i - w r i) ^ 2)
          ((z t i - w t i) *
            (z t i * K (x t) i - w t i * K (y t) i)) (Ici t) t := by
      intro i
      have hxp : 0 < x t i := hpositive (x t) (hxmem t htc) i
      have hyp : 0 < y t i := hpositive (y t) (hymem t htc) i
      have hz_ne : z t i ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxp)
      have hw_ne : w t i ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hyp)
      have hxcoef :
          x t i * K (x t) i / (2 * z t i) = z t i * K (x t) i / 2 := by
        apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hz_ne)).2
        rw [← hzsq t htc i]
        ring
      have hycoef :
          y t i * K (y t) i / (2 * w t i) = w t i * K (y t) i / 2 := by
        apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hw_ne)).2
        rw [← hwsq t htc i]
        ring
      have hzderiv : HasDerivWithinAt (fun r => z r i)
          (z t i * K (x t) i / 2) (Ici t) t := by
        have hd : HasDerivWithinAt (fun r => z r i)
            (x t i * K (x t) i / (2 * z t i)) (Ici t) t :=
          (hxderiv t ht i).sqrt (ne_of_gt hxp)
        rwa [hxcoef] at hd
      have hwderiv : HasDerivWithinAt (fun r => w r i)
          (w t i * K (y t) i / 2) (Ici t) t := by
        have hd : HasDerivWithinAt (fun r => w r i)
            (y t i * K (y t) i / (2 * w t i)) (Ici t) t :=
          (hyderiv t ht i).sqrt (ne_of_gt hyp)
        rwa [hycoef] at hd
      have hd : HasDerivWithinAt (fun r => (z r i - w r i) ^ 2)
          ((2 : ℝ) * (z t i - w t i) ^ (2 - 1) *
            (z t i * K (x t) i / 2 - w t i * K (y t) i / 2)) (Ici t) t :=
        (hzderiv.sub hwderiv).fun_pow 2
      have hcoef :
          (2 : ℝ) * (z t i - w t i) ^ (2 - 1) *
              (z t i * K (x t) i / 2 - w t i * K (y t) i / 2) =
            (z t i - w t i) *
              (z t i * K (x t) i - w t i * K (y t) i) := by
        norm_num <;> ring
      rwa [hcoef] at hd
    exact HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hcoord i)

  -- The exact polynomial split is proved, rather than supplied as a premise.
  have hsplit : ∀ t ∈ Icc a b,
      Hprime t =
        (1 / 2 : ℝ) * (∑ i, (x t i - y t i) * (K (x t) i - K (y t) i)) +
        (1 / 2 : ℝ) *
          (∑ i, (z t i - w t i) ^ 2 * (K (x t) i + K (y t) i)) := by
    intro t ht
    dsimp only [Hprime]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hzsq t ht i, ← hwsq t ht i]
    ring

  have hHbound : ∀ t ∈ Ico a b, Hprime t ≤ C * H t := by
    intro t ht
    have htc : t ∈ Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    have ha := hanti (x t) (hxmem t htc) (y t) (hymem t htc)
    have hs :
        (∑ i, (z t i - w t i) ^ 2 * (K (x t) i + K (y t) i)) ≤
          2 * C * H t := by
      calc
        (∑ i, (z t i - w t i) ^ 2 * (K (x t) i + K (y t) i)) ≤
            ∑ i, (z t i - w t i) ^ 2 * (2 * C) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg (z t i - w t i))
          have hxC := hupper (x t) (hxmem t htc) i
          have hyC := hupper (y t) (hymem t htc) i
          linarith only [hxC, hyC]
        _ = 2 * C * H t := by
          rw [← Finset.sum_mul]
          exact mul_comm (H t) (2 * C)
    rw [hsplit t htc]
    linarith only [ha, hs]

  -- Use signed right slopes; no absolute derivative bound is needed.
  have hHslopes : ∀ t ∈ Ico a b, ∀ r, Hprime t < r →
      ∃ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (H s - H t) < r := by
    intro t ht r hr
    simpa only [slope_def_field, div_eq_inv_mul] using
      (hHderiv t ht).liminf_right_slope_le hr

  have hstability : ∀ t ∈ Icc a b,
      H t ≤ Real.exp (C * (t - a)) * H a := by
    intro t ht
    have hg := le_gronwallBound_of_liminf_deriv_right_le
      (f := H) (f' := Hprime) (δ := H a) (K := C) (ε := 0)
      hHcont hHslopes (le_refl (H a))
      (fun s hs => by simpa only [add_zero] using hHbound s hs) t ht
    rw [gronwallBound_ε0] at hg
    calc
      H t ≤ H a * Real.exp (C * (t - a)) := hg
      _ = Real.exp (C * (t - a)) * H a := mul_comm _ _

  constructor
  · exact hstability
  · intro hinit t ht
    have hHa : H a = 0 := by simp [H, z, w, hinit]
    have hHt_le : H t ≤ 0 := by
      simpa only [hHa, mul_zero] using hstability t ht
    have hHt : H t = 0 := le_antisymm hHt_le (hHnonneg t)
    funext i
    have hsqi : (z t i - w t i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
          sq_nonneg (z t j - w t j))).mp hHt i (Finset.mem_univ i)
    have hzw : z t i = w t i := sub_eq_zero.mp (sq_eq_zero_iff.mp hsqi)
    calc
      x t i = (z t i) ^ 2 := (hzsq t ht i).symm
      _ = (w t i) ^ 2 := congrArg (fun r : ℝ => r ^ 2) hzw
      _ = y t i := hwsq t ht i

set_option pp.all true in
#check @CFMP164Transient.original_multiplicative_flow_check

#print axioms CFMP164Transient.original_multiplicative_flow_check
#print axioms le_gronwallBound_of_liminf_deriv_right_le
#print axioms HasDerivWithinAt.sqrt
#print axioms HasDerivWithinAt.liminf_right_slope_le
