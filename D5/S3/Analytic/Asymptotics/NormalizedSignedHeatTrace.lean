/- GID: D5/S3/Analytic/Asymptotics/NormalizedSignedHeatTrace
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/NormalizedSignedHeatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonpositive signed mass prefixes give a strictly increasing normalized heat trace. -/

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import OmegaBuild.Commands

compile_only_with_mathlib

open Finset Set

namespace D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace

private theorem signed_sum_neg (n : ℕ) (g w : ℕ → ℝ)
    (hprefix : ∀ k ≤ n, (∑ i ∈ range k, g i) ≤ 0)
    (htotal : (∑ i ∈ range n, g i) < 0)
    (hpos : 0 < w (n - 1))
    (hstep : ∀ i ∈ range (n - 1), w (i + 1) ≤ w i) :
    (∑ i ∈ range n, g i * w i) < 0 := by
  simp_rw [mul_comm (g _)]
  rw [show (∑ i ∈ range n, w i * g i) = ∑ i ∈ range n, w i • g i by rfl,
    sum_range_by_parts]
  change w (n - 1) * (∑ i ∈ range n, g i) -
    (∑ i ∈ range (n - 1), (w (i + 1) - w i) * (∑ j ∈ range (i + 1), g j)) < 0
  have hs : 0 ≤ ∑ i ∈ range (n - 1), (w (i + 1) - w i) * (∑ j ∈ range (i + 1), g j) := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hstep i hi))
      (hprefix (i + 1) (by have := mem_range.mp hi; omega))
  exact sub_neg.mpr ((mul_neg_of_pos_of_neg hpos htotal).trans_le hs)

private theorem heat_weight_antitone :
    AntitoneOn (fun u : ℝ => (1 + u) * Real.exp (-u)) (Ici 0) := by
  have hd (u : ℝ) : HasDerivAt (fun t : ℝ => (1+t) * Real.exp (-t))
      (-u * Real.exp (-u)) u := by
    have h₁ : HasDerivAt (fun t : ℝ => 1+t) 1 u := by
      simpa only [zero_add] using (hasDerivAt_id' u).const_add (1 : ℝ)
    have h₂ : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-u)) u := by
      simpa using (hasDerivAt_id u).neg.exp
    convert h₁.mul h₂ using 1
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
  intro u hu
  rw [(hd u).deriv]
  have hu0 : 0 ≤ u := interior_subset hu
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu0) (Real.exp_pos _).le

private theorem cutoff_heat_component (n : ℕ) (g z : ℕ → ℝ)
    (hprefix : ∀ k ≤ n, (∑ i ∈ range k, g i) ≤ 0)
    (htotal : (∑ i ∈ range n, g i) < 0)
    (hz : ∀ i, 0 ≤ z i) (horder : Monotone z) :
    StrictAntiOn (fun x : ℝ => x * ∑ i ∈ range n, g i * Real.exp (-(z i / x)))
      (Ioi 0) := by
  have hterm (x : ℝ) (hx : 0 < x) (i : ℕ) :
      HasDerivAt (fun t : ℝ => g i * (t * Real.exp (-(z i/t))))
        (g i * ((1 + z i/x) * Real.exp (-(z i/x)))) x := by
    have hdivide : HasDerivAt (fun t : ℝ => z i / t) (-(z i/x^2)) x := by
      convert (hasDerivAt_const x (z i)).fun_div (hasDerivAt_id' x) hx.ne' using 1
      ring
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(z i/t)))
        (Real.exp (-(z i/x)) * (z i/x^2)) x := by
      simpa only [neg_neg] using hdivide.fun_neg.exp
    convert ((hasDerivAt_id' x).fun_mul hexp).const_mul (g i) using 1
    field_simp
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t : ℝ => t * ∑ i ∈ range n, g i * Real.exp (-(z i/t)))
        (∑ i ∈ range n, g i * ((1 + z i/x) * Real.exp (-(z i/x)))) x := by
    convert (HasDerivAt.fun_sum (u := range n) (fun i _ => hterm x hx i)) using 1
    funext t
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx0 : 0 < x := interior_subset hx
  rw [(hderiv x hx0).deriv]
  apply signed_sum_neg n g (fun i => (1 + z i/x) * Real.exp (-(z i/x))) hprefix htotal
  · positivity [hz (n - 1)]
  · intro i _
    apply heat_weight_antitone (div_nonneg (hz i) hx0.le)
      (div_nonneg (hz (i + 1)) hx0.le)
    exact div_le_div_of_nonneg_right (horder (by omega)) hx0.le


/-- The normalized signed heat trace is strictly increasing under a
strict differential inequality for the negative denominator. -/
theorem normalized_cutoff_heat_strictMono (n : ℕ) (g z : ℕ → ℝ) (B dB : ℝ → ℝ) (b : ℝ)
    (hprefix : ∀ k ≤ n, (∑ i ∈ range k, g i) ≤ 0)
    (htotal : (∑ i ∈ range n, g i) < 0)
    (hz : ∀ i, 0 ≤ z i) (horder : Monotone z)
    (hB : ∀ x ∈ Ioc 0 b, B x < 0)
    (hderiv : ∀ x ∈ Ioc 0 b, HasDerivAt B (dB x) x)
    (hgap : ∀ x ∈ Ioc 0 b, B x < x * dB x) :
    StrictMonoOn (fun x : ℝ => (x^2 * ∑ i ∈ range n, g i * Real.exp (-(z i / x))) / B x)
      (Ioc 0 b) := by
  let F (x : ℝ) := x * ∑ i ∈ range n, g i * Real.exp (-(z i / x))
  let G (x : ℝ) := x / B x
  have hFanti : StrictAntiOn F (Ioi 0) := cutoff_heat_component n g z hprefix htotal hz horder
  have hFneg (x : ℝ) (hx : 0 < x) : F x < 0 := by
    apply mul_neg_of_pos_of_neg hx
    apply signed_sum_neg n g (fun i => Real.exp (-(z i/x))) hprefix htotal (Real.exp_pos _)
    intro i _
    exact Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right (horder (by omega)) hx.le))
  have hGderiv (x : ℝ) (hx : x ∈ Ioc 0 b) :
      HasDerivAt G ((B x - x*dB x) / (B x)^2) x := by
    convert (hasDerivAt_id' x).fun_div (hderiv x hx) (hB x hx).ne using 1
    ring
  have hGanti : StrictAntiOn G (Ioc 0 b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
      (fun x hx => (hGderiv x hx).continuousAt.continuousWithinAt)
    intro x hx_int
    have hx := interior_subset hx_int
    rw [(hGderiv x hx).deriv]
    exact div_neg_of_neg_of_pos (sub_neg.mpr (hgap x hx)) (sq_pos_of_ne_zero (hB x hx).ne)
  intro x hx y hy hxy
  have hp : F x * G x < F y * G y := by
    have hGx : G x < 0 := div_neg_of_pos_of_neg hx.1 (hB x hx)
    calc F x * G x < F y * G x := mul_lt_mul_of_neg_right (hFanti hx.1 hy.1 hxy) hGx
      _ < F y * G y := mul_lt_mul_of_neg_left (hGanti hx hy hxy) (hFneg y hy.1)
  convert hp using 1 <;> dsimp [F,G] <;> ring

end D5.S3.Analytic.Asymptotics.NormalizedSignedHeatTrace
