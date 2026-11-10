/- GID: D5/S3/Analytic/ConvexBarrier/RecessionOneDimensional
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/RecessionOneDimensional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.DikinOneDimensional
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The standard original-ray self-concordance estimate. The derivative
comparison is the finite-interval integration: no integral estimate, sign,
or limiting value of g is supplied as a hidden conclusion. The ONLY sign
premise here is g(t) <= 0; OriginalConeRecession derives it from the actual
barrier. The sequence of finite intervals has lengths n/sqrt(q(0)).

SOURCE ONLY, UNCOMPILED. No kernel/CI/official or novelty claim.
-/

open Set Filter
open scoped Topology

namespace D5.S3.Analytic.ConvexBarrier

/-- A small wrapper around Mathlib's actual mean-value theorem. -/
theorem monotoneOn_from_hasDerivAt {S : Set ℝ} (hS : Convex ℝ S)
    {f d : ℝ → ℝ} (hd : ∀ t ∈ S, HasDerivAt f (d t) t)
    (hn : ∀ t ∈ S, 0 ≤ d t) : MonotoneOn f S := by
  apply monotoneOn_of_deriv_nonneg hS
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact hn t (interior_subset ht)

/-- The lower Hessian estimate, obtained by differentiating 1/sqrt(q).
All endpoints of the finite interval are covered by the derivative data. -/
theorem recession_hessian_lower {q c : ℝ → ℝ}
    (hq : ∀ t : ℝ, 0 ≤ t → HasDerivAt q (c t) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < q t)
    (hsc : ∀ t : ℝ, 0 ≤ t → |c t| ≤ 2*q t*Real.sqrt (q t))
    {t : ℝ} (ht : 0 ≤ t) :
    ((Real.sqrt (q 0))⁻¹+t)⁻¹ ^ 2 ≤ q t := by
  have hs0 : 0 < Real.sqrt (q 0) := Real.sqrt_pos.mpr (hpos 0 le_rfl)
  have hst : 0 < Real.sqrt (q t) := Real.sqrt_pos.mpr (hpos t ht)
  have hm : 0 < (Real.sqrt (q 0))⁻¹+t := add_pos_of_pos_of_nonneg (inv_pos.mpr hs0) ht
  have hlip := reciprocalHessian_lipschitz ht
    (fun u hu => hq u hu.1) (fun u hu => hpos u hu.1)
    (fun u hu => hsc u hu.1)
  have hr : (Real.sqrt (q t))⁻¹ ≤ (Real.sqrt (q 0))⁻¹+t := by
    have hh := (abs_le.mp hlip).2
    dsimp [reciprocalHessian] at hh
    linarith
  have hmul : 1 ≤ ((Real.sqrt (q 0))⁻¹+t)*Real.sqrt (q t) := by
    rw [inv_eq_one_div] at hr
    exact (div_le_iff₀ hst).mp hr
  have hroot : ((Real.sqrt (q 0))⁻¹+t)⁻¹ ≤ Real.sqrt (q t) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hm).mpr
    nlinarith
  calc
    ((Real.sqrt (q 0))⁻¹+t)⁻¹ ^ 2 ≤ (Real.sqrt (q t))^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (inv_pos.mpr hm).le hroot
    _ = q t := Real.sq_sqrt (hpos t ht).le

/-- Explicit finite-T integration by a derivative comparison:
`(g(t)+(r+t)^(-1))' = q(t)-(r+t)^(-2) >= 0`.
Thus no integral inequality is assumed. -/
theorem recession_finite_bound {g q c : ℝ → ℝ}
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (q t) t)
    (hq : ∀ t : ℝ, 0 ≤ t → HasDerivAt q (c t) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < q t)
    (hsc : ∀ t : ℝ, 0 ≤ t → |c t| ≤ 2*q t*Real.sqrt (q t))
    (hsign : ∀ t : ℝ, 0 ≤ t → g t ≤ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    Real.sqrt (q 0) - ((Real.sqrt (q 0))⁻¹+T)⁻¹ ≤ -g 0 := by
  let r := (Real.sqrt (q 0))⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr (hpos 0 le_rfl))
  have hd : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun u => g u+(r+u)⁻¹) (q t-(r+t)⁻¹ ^ 2) t := by
    intro t ht
    have hm : r+t ≠ 0 := (add_pos_of_pos_of_nonneg hr ht.1).ne'
    have hi : HasDerivAt (fun u : ℝ => (r+u)⁻¹) (-(r+t)⁻¹ ^ 2) t := by
      convert ((hasDerivAt_const t r).add (hasDerivAt_id t)).inv hm using 1
      · funext u
        simp [add_comm]
      · simp [div_eq_mul_inv, pow_two]
    convert (hg t ht.1).add hi using 1
  have hmono := monotoneOn_from_hasDerivAt (convex_Icc (0 : ℝ) T) hd (fun t ht => by
    have hh := recession_hessian_lower hq hpos hsc ht.1
    exact sub_nonneg.mpr hh)
  have hh := hmono (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  have hTsign := hsign T hT
  have hri : r⁻¹ = Real.sqrt (q 0) := inv_inv _
  simp only [add_zero, hri] at hh
  dsimp only [r] at hh
  linarith

/-- Reusable recession theorem. In particular, g is not required to
converge, nor to tend to zero, and no finite boundary blowup is used. -/
theorem selfConcordant_recession {g q c : ℝ → ℝ}
    (hg : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (q t) t)
    (hq : ∀ t : ℝ, 0 ≤ t → HasDerivAt q (c t) t)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 < q t)
    (hsc : ∀ t : ℝ, 0 ≤ t → |c t| ≤ 2*q t*Real.sqrt (q t))
    (hsign : ∀ t : ℝ, 0 ≤ t → g t ≤ 0) :
    Real.sqrt (q 0) ≤ -g 0 := by
  let s := Real.sqrt (q 0)
  have hs : 0 < s := Real.sqrt_pos.mpr (hpos 0 le_rfl)
  have hfinite (n : ℕ) : s-s*(1/((n : ℝ)+1)) ≤ -g 0 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hh := recession_finite_bound hg hq hpos hsc hsign
      (T := (n : ℝ)*s⁻¹) (mul_nonneg hn (inv_pos.mpr hs).le)
    have he : (s⁻¹+(n : ℝ)*s⁻¹)⁻¹ = s*(1/((n : ℝ)+1)) := by
      rw [show s⁻¹+(n : ℝ)*s⁻¹ = s⁻¹*((n : ℝ)+1) by ring,
        mul_inv_rev, inv_inv]
      simp only [one_div]
      ring
    change s-(s⁻¹+(n : ℝ)*s⁻¹)⁻¹ ≤ -g 0 at hh
    rwa [he] at hh
  have hlim : Tendsto (fun n : ℕ => s-s*(1/((n : ℝ)+1))) atTop (𝓝 s) := by
    have hh := (tendsto_const_nhds (x := s)).sub
      ((tendsto_const_nhds (x := s)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [mul_zero, sub_zero] using hh
  exact le_of_tendsto' hlim hfinite

end D5.S3.Analytic.ConvexBarrier
