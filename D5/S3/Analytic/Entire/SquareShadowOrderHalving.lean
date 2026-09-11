/- GID: D5/S3/Analytic/Entire/SquareShadowOrderHalving
   generality: G
   mirror-B: D5/B/S3/Analytic/Entire/SquareShadowOrderHalving
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Circular maximum modulus and extended-real growth order under a square shadow. -/

import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Metric Filter


namespace D5.S3.Analytic.Entire.SquareShadowOrderHalving

/-- Supremum of the norm on a circle. For continuous functions and nonnegative radii,
this is an attained maximum; no boundedness claim is made for arbitrary functions. -/
def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' sphere 0 r)

/-- The radius-zero circle consists of the origin. -/
theorem max_modulus_zero (f : ℂ → ℂ) : maxModulus f 0 = ‖f 0‖ := by
  simp [maxModulus]

/-- Compactness realizes the circular supremum, including at radius zero. -/
theorem max_modulus_attained {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 ≤ r) :
    ∃ z ∈ sphere (0 : ℂ) r, maxModulus f r = ‖f z‖ := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr) hf.norm.continuousOn
  refine ⟨z, hz, ?_⟩
  change sSup ((fun w => ‖f w‖) '' sphere 0 r) = ‖f z‖
  apply IsLUB.csSup_eq _ ((NormedSpace.sphere_nonempty.mpr hr).image _)
  apply IsGreatest.isLUB
  refine ⟨mem_image_of_mem _ hz, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hmax hw

private theorem norm_le_max {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) r) : ‖f z‖ ≤ maxModulus f r := by
  exact le_csSup ((isCompact_sphere (0 : ℂ) r).bddAbove_image hf.norm.continuousOn)
    (mem_image_of_mem _ hz)

/-- Squaring the argument rescales the maximum modulus by the square root of the radius.
Continuity suffices; the entire square shadow in particular satisfies these hypotheses. -/
theorem max_modulus_square_shadow {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ z, F z = G (z ^ 2)) {r : ℝ} (hr : 0 ≤ r) :
    maxModulus G r = maxModulus F (Real.sqrt r) := by
  obtain rfl | _hrpos := hr.eq_or_lt
  · simpa only [Real.sqrt_zero, max_modulus_zero, zero_pow (by decide : 2 ≠ 0)]
      using (congrArg norm (hFG 0)).symm
  obtain ⟨w, hw, hwmax⟩ := max_modulus_attained hG hr
  obtain ⟨z, hz, hzmax⟩ := max_modulus_attained hF (Real.sqrt_nonneg r)
  apply le_antisymm
  · let u : ℂ := w.sqrt
    have hu : u ^ 2 = w := Complex.cpow_nat_inv_pow w (by decide : 2 ≠ 0)
    have hunorm : ‖u‖ = Real.sqrt r := by
      have h := congrArg norm hu
      rw [norm_pow, mem_sphere_zero_iff_norm.mp hw] at h
      rw [← h, Real.sqrt_sq (norm_nonneg u)]
    rw [hwmax, ← hu, ← hFG u]
    exact norm_le_max hF (mem_sphere_zero_iff_norm.mpr hunorm)
  · rw [hzmax, hFG z]
    apply norm_le_max hG
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_pow, mem_sphere_zero_iff_norm.mp hz, Real.sq_sqrt hr]

/-- Extended-real growth order. The real logarithmic quotient is coerced before taking
the limsup, retaining infinite order. Real.log and division are total at small radii;
only the tail at positive infinity contributes. The zero function has order zero. -/
def order (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ =>
    ((Real.log (Real.log (maxModulus f r)) / Real.log r : ℝ) : EReal)) atTop


/-- The square shadow halves growth order, also for infinite order. -/
theorem order_square_shadow {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ z, F z = G (z ^ 2)) : order G = order F / 2 := by
  let q : ℝ → EReal := fun r => (Real.log (Real.log (maxModulus F r)) / Real.log r : ℝ)
  have hq : (fun r : ℝ =>
      ((Real.log (Real.log (maxModulus G r)) / Real.log r : ℝ) : EReal)) =ᶠ[atTop]
      (fun r => ((1 / 2 : ℝ) : EReal) * q (Real.sqrt r)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    rw [max_modulus_square_shadow hF hG hFG hr]
    dsimp [q]
    rw [← EReal.coe_mul, Real.log_sqrt hr]
    congr 1
    ring
  unfold order
  rw [limsup_congr hq, EReal.limsup_const_mul_of_nonneg_of_ne_top]
  · change ((1 / 2 : ℝ) : EReal) * limsup (q ∘ Real.sqrt) atTop = _
    rw [limsup_comp, Real.map_sqrt_atTop]
    simp only [q, div_eq_mul_inv, one_mul, EReal.coe_inv, EReal.mul_comm]
    rfl
  · exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · exact EReal.coe_ne_top _

/-- A square shadow of an order-one function has order one half. -/
theorem order_half_of_order_one {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ z, F z = G (z ^ 2)) (horder : order F = 1) : order G = 1 / 2 := by
  rw [order_square_shadow hF hG hFG, horder]

#print axioms max_modulus_zero
#print axioms max_modulus_attained
#print axioms max_modulus_square_shadow
#print axioms order_square_shadow
#print axioms order_half_of_order_one

end D5.S3.Analytic.Entire.SquareShadowOrderHalving
