import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace CFMPConvexCoercivity292Transient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- A strict gap on one compact sphere gives a uniform positive radial slope
outside that sphere. The sphere may be empty. No global Hessian bound is used. -/
theorem convex_sphere_gap_linear (f : E → ℝ) (hf : Continuous f)
    (hconv : ConvexOn ℝ Set.univ f) (a : E) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ x ∈ Metric.sphere a r, f a < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : E, r ≤ ‖x-a‖ →
      f a + c * ‖x-a‖ ≤ f x := by
  obtain ⟨b,hb,hbf⟩ := (isCompact_sphere a r).exists_forall_le'
    hf.continuousOn hgap
  refine ⟨(b-f a)/r,div_pos (sub_pos.mpr hb) hr,?_⟩
  intro x hx
  have hR : 0 < ‖x-a‖ := hr.trans_le hx
  let t : ℝ := r / ‖x-a‖
  have ht : 0 < t := div_pos hr hR
  have ht1 : t ≤ 1 := (div_le_one₀ hR).2 hx
  let y : E := (1-t) • a + t • x
  have hy : y-a = t • (x-a) := by dsimp [y]; module
  have hynorm : ‖y-a‖ = r := by
    rw [hy,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    field_simp
  have hys : y ∈ Metric.sphere a r := by
    simpa only [Metric.mem_sphere,dist_eq_norm] using hynorm
  have hj : f y ≤ (1-t)*f a+t*f x :=
    hconv.2 (Set.mem_univ a) (Set.mem_univ x)
      (sub_nonneg.mpr ht1) ht.le (by ring)
  have hraw : b-f a ≤ t*(f x-f a) := by
    have := hbf y hys
    nlinarith
  have hscaled : (b-f a)*‖x-a‖ ≤ r*(f x-f a) := by
    calc
      _ ≤ (t*(f x-f a))*‖x-a‖ :=
        mul_le_mul_of_nonneg_right hraw (norm_nonneg _)
      _ = _ := by dsimp [t]; field_simp
  have hslope : (b-f a)/r*‖x-a‖ ≤ f x-f a := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hr]
    nlinarith
  linarith

/-- Properness of the ambient space turns a positive sphere gap into
coercivity and a global minimum, including zero-dimensional ambient spaces. -/
theorem convex_sphere_gap_coercive_minimum (f : E → ℝ) (hf : Continuous f)
    (hconv : ConvexOn ℝ Set.univ f) (a : E) (r : ℝ) (hr : 0 < r)
    (hgap : ∀ x ∈ Metric.sphere a r, f a < f x) :
    Tendsto f (cocompact E) atTop ∧ ∃ x : E, ∀ y : E, f x ≤ f y := by
  obtain ⟨c,hc,hbound⟩ := convex_sphere_gap_linear f hf hconv a r hr hgap
  have hcoercive : Tendsto f (cocompact E) atTop := by
    apply tendsto_atTop.2
    intro B
    have he : ∀ᶠ x : E in cocompact E,
        max (r+‖a‖) ((B-f a)/c+‖a‖) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [he] with x hx
    have hn : ‖x‖-‖a‖ ≤ ‖x-a‖ := norm_sub_norm_le x a
    have hR : r ≤ ‖x-a‖ := by
      have := (le_max_left (r+‖a‖) ((B-f a)/c+‖a‖)).trans hx
      linarith
    have hB : (B-f a)/c ≤ ‖x-a‖ := by
      have := (le_max_right (r+‖a‖) ((B-f a)/c+‖a‖)).trans hx
      linarith
    have hmul := (div_le_iff₀ hc).1 hB
    have : B ≤ f a+c*‖x-a‖ := by nlinarith
    exact this.trans (hbound x hR)
  exact ⟨hcoercive,hf.exists_forall_le hcoercive⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- First-order minimality is obtained by applying the existing scalar
convex secant bound to every affine line through the critical point. -/
private theorem critical_global_minimum (f : E → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (a : E)
    (hcritical : HasFDerivAt f (0 : E →L[ℝ] ℝ) a) :
    ∀ x : E, f a ≤ f x := by
  intro x
  let g : ℝ → ℝ := fun t => f (AffineMap.lineMap a x t)
  have hgc : ConvexOn ℝ Set.univ g := by
    simpa only [Set.preimage_univ,g,Function.comp_def] using
      hconv.comp_affineMap (AffineMap.lineMap a x)
  have hd : HasDerivAt g 0 0 := by
    have hcritical0 : HasFDerivAt f (0 : E →L[ℝ] ℝ)
        (AffineMap.lineMap a x (0 : ℝ)) := by simpa using hcritical
    have hd0 := hcritical0.comp_hasDerivAt 0
      (AffineMap.hasDerivAt_lineMap (a := a) (b := x) (x := (0 : ℝ)))
    simpa only [g,Function.comp_def,AffineMap.lineMap_apply_zero,ContinuousLinearMap.zero_apply] using hd0
  have hsec := hgc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hd
  simpa [g,slope_def_field,sub_nonneg] using hsec

/-- The local strict convexity required in the classical covolume argument
is sufficient: no uniform or strictly positive Hessian is required globally. -/
theorem convex_critical_locally_strict_coercive
    (f : E → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ Set.univ f)
    (a : E) (hcritical : HasFDerivAt f (0 : E →L[ℝ] ℝ) a)
    (R : ℝ) (hR : 0 < R) (hstrict : StrictConvexOn ℝ (Metric.ball a R) f) :
    (∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ x : E, r ≤ ‖x-a‖ →
      f a+c*‖x-a‖ ≤ f x) ∧ Tendsto f (cocompact E) atTop := by
  have hmin := critical_global_minimum f hconv a hcritical
  let r := R/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  have hgap : ∀ x ∈ Metric.sphere a r, f a < f x := by
    intro x hx
    have hdist : dist x a = r := Metric.mem_sphere.mp hx
    have hxb : x ∈ Metric.ball a R := Metric.mem_ball.mpr (hdist.trans_lt hrR)
    have hab : a ∈ Metric.ball a R := Metric.mem_ball_self hR
    by_contra hnot
    have heq : f a = f x := le_antisymm (hmin x) (not_lt.mp hnot)
    have hma : IsMinOn f (Metric.ball a R) a := fun y _ => hmin y
    have hmx : IsMinOn f (Metric.ball a R) x := by
      intro y _
      rw [← heq]
      exact hmin y
    have hax : a = x := hstrict.eq_of_isMinOn hma hmx hab hxb
    have : r = 0 := by simpa [← hax] using hdist.symm
    linarith
  obtain ⟨c,hc,hbound⟩ := convex_sphere_gap_linear f hf hconv a r hr hgap
  exact ⟨⟨r,c,hr,hc,hbound⟩,
    (convex_sphere_gap_coercive_minimum f hf hconv a r hr hgap).1⟩

end CFMPConvexCoercivity292Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPConvexCoercivity292Transient.convex_sphere_gap_linear,
      ``CFMPConvexCoercivity292Transient.convex_sphere_gap_coercive_minimum,
      ``CFMPConvexCoercivity292Transient.convex_critical_locally_strict_coercive] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP292 radial coercivity declaration absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP292 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP292 CHECKED {name} axioms={axioms}"
