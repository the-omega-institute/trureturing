/- GID: D5/S3/Analytic/CothBernoulliDegree/Kernel
   generality: G
   mirror-B: D5/B/S3/Analytic/CothBernoulliDegree/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic, mathlib/module/Mathlib.Topology.Algebra.InfiniteSum.Real, mathlib/module/Mathlib.Analysis.Real.Pi.Bounds, mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real, mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv]
   utility: none
   digest: Rational kernel derivative certificates and uniform phase and series estimates. -/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Tactic

namespace D5.S3.Analytic.CothBernoulliDegree.Kernel

open Set Real
open scoped BigOperators

private lemma arctan_chord (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Real.pi / 4 * x ≤ Real.arctan x := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) 1) Real.arctan := by
    apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
      Real.continuous_arctan.continuousOn
      Real.differentiable_arctan.differentiableOn
    intro a ha b hb hab
    rw [Real.deriv_arctan]
    apply one_div_le_one_div_of_le (by positivity)
    have ha0 : 0 ≤ a := (interior_subset ha).1
    nlinarith
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : (1-x)+x=1)
  simpa [Real.arctan_one, mul_comm] using h

private lemma log_sq_chord (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : Real.log (1+x^2) ≤ x * Real.log 2 := by
  have hd (a : ℝ) : HasDerivAt (fun y : ℝ => Real.log (1+y^2)) (2*a/(1+a^2)) a := by
    have hpow : HasDerivAt (fun y : ℝ => 1+y^2) (2*a) a := by
      convert ((hasDerivAt_id a).pow 2).const_add 1 using 1 <;> simp <;> ring
    convert hpow.log (by positivity) using 1 <;> ring
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) (fun y : ℝ => Real.log (1+y^2)) := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
      (fun a _ => (hd a).continuousAt.continuousWithinAt)
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt)
    intro a ha b hb hab
    rw [(hd a).deriv, (hd b).deriv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have ha0 : 0 ≤ a := (interior_subset ha).1
    have hb1 : b ≤ 1 := (interior_subset hb).2
    have hb0 : 0 ≤ b := ha0.trans hab
    have ha1 : a ≤ 1 := hab.trans hb1
    have hprod : a*b ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hprod)]
  have h := hc.2 (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : (1-x)+x=1)
  norm_num at h
  simpa using h

private lemma phase_sin_bound (M : ℝ) (hM : 5 ≤ M) :
    Real.sin (M * Real.arctan (5/M)) ≤ - Real.sqrt 2 / 2 := by
  have hMp : 0 < M := by linarith
  have hx : (5/M : ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hMp).2 hM⟩
  have hlo := mul_le_mul_of_nonneg_left (arctan_chord (5/M) hx) hMp.le
  have hhi := mul_le_mul_of_nonneg_left (Real.arctan_le_self hx.1) hMp.le
  have heq : M * (Real.pi / 4 * (5/M)) = 5*Real.pi/4 := by field_simp
  have heq' : M * (5/M) = 5 := by field_simp
  rw [heq] at hlo
  rw [heq'] at hhi
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hd : |M * Real.arctan (5/M) - 3*Real.pi/2| ≤ Real.pi/4 := by
    rw [abs_le]; constructor <;> linarith
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (M * Real.arctan (5/M) - 3*Real.pi/2))
    (show Real.pi/4 ≤ Real.pi by linarith [Real.pi_pos]) hd
  rw [Real.cos_abs, Real.cos_pi_div_four] at hc
  have htrig : Real.sin (M * Real.arctan (5/M)) =
      -Real.cos (M * Real.arctan (5/M) - 3*Real.pi/2) := by
    rw [show M * Real.arctan (5/M) - 3*Real.pi/2 =
      M * Real.arctan (5/M) - Real.pi/2 - Real.pi by ring,
      Real.cos_sub_pi, Real.cos_sub_pi_div_two]
    ring
  rw [htrig]
  linarith

private lemma amplitude_bound (M : ℝ) (hM : 5 ≤ M) :
    Real.sqrt 2 / 8 ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := by
  have hMp : 0 < M := by linarith
  have hx : (5/M : ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one hMp).2 hM⟩
  have hl := mul_le_mul_of_nonneg_left (log_sq_chord (5/M) hx) hMp.le
  have heq : M * ((5/M)* Real.log 2) = 5*Real.log 2 := by field_simp
  rw [heq] at hl
  have he : (2:ℝ)^(-(5:ℝ)/2) ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hv : (2:ℝ)^(-(5:ℝ)/2) = Real.sqrt 2 / 8 := by
    rw [show -(5:ℝ)/2 = 1/2-3 by norm_num, Real.rpow_sub (by norm_num)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rwa [hv] at he

lemma phase_bound (M : ℝ) (hM : 5 ≤ M) :
    (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) * Real.sin (M*Real.arctan (5/M)) ≤ -(1:ℝ)/8 := by
  have ha := amplitude_bound M hM
  have hs := phase_sin_bound M hM
  have hp : 0 ≤ (1+(5/M)^2 : ℝ)^(-M/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left hs hp
  have h' := mul_le_mul_of_nonpos_right ha (show -Real.sqrt 2 / 2 ≤ 0 by have := Real.sqrt_nonneg (2:ℝ); linarith)
  have hsq : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith

open scoped BigOperators

private lemma term_bound (k : ℕ) :
    1 / ((k : ℝ) + 2)^5 ≤
      (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : 0 < (k : ℝ) + 1 := by positivity
  have h2 : 0 < (k : ℝ) + 2 := by positivity
  have hs : 4 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2)^2 := by nlinarith [sq_nonneg (k : ℝ)]
  have hs' : 4 ≤ ((k : ℝ) + 2)^2 := by nlinarith
  have hp : 16 * ((k : ℝ) + 1) ≤ ((k : ℝ) + 2)^4 := by
    nlinarith [mul_le_mul hs hs' (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ ((k : ℝ) + 2)^2)]
  have heq :
      (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 =
        1 / (16 * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
    ring
  rw [heq]
  apply one_div_le_one_div_of_le (by positivity)
  convert mul_le_mul_of_nonneg_right hp h2.le using 1; ring

lemma tail_bound (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((k : ℝ) + 2)^(2*n+1)) ≤ 1/16 := by
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro N
  have hterm (k : ℕ) :
      1 / ((k : ℝ) + 2)^(2*n+1) ≤
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 := by
    apply le_trans _ (term_bound k)
    apply one_div_le_one_div_of_le (by positivity : 0 < ((k : ℝ) + 2)^5)
    exact pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2) (by omega)
  calc
    _ ≤ ∑ k ∈ Finset.range N,
        (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) / 16 :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = (1 - 1 / ((N : ℝ) + 1)) / 16 := by
      rw [← Finset.sum_div]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_div_one,
        add_assoc, one_add_one_eq_two] using
        Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) N
    _ ≤ 1/16 := by
      have : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith


end D5.S3.Analytic.CothBernoulliDegree.Kernel
