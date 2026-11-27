import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar centered-difference comparison along the Wu cubic conditioning segment. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter
open scoped Topology

namespace D5.S3.Quantum.Semigroups.WuCubicCenteredComparison

/-- Strictly positive local centered differences force strict convexity on the segment. -/
theorem strictConvexOn_of_centered_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hcenter : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      2 * f x < f (x + t) + f (x - t)) :
    StrictConvexOn ℝ (Icc 0 1) f := by
  refine LinearOrder.strictConvexOn_of_lt (convex_Icc 0 1) ?_
  intro a ha b hb hab p q hp hq hpq
  simp only [smul_eq_mul]
  let z := p * a + q * b
  have hz : z ∈ Ioo a b := by
    constructor
    · dsimp [z]
      linear_combination q * hab - a * hpq
    · dsimp [z]
      linear_combination p * hab + b * hpq
  let chordSlope := (f b - f a) / (b - a)
  let chord := fun u : ℝ => f a + (u - a) * chordSlope
  have hchord_a : chord a = f a := by simp [chord]
  have hchord_b : chord b = f b := by
    simp only [chord, chordSlope, mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  have hchord_z : chord z = p * f a + q * f b := by
    rw [← hchord_a, ← hchord_b]
    dsimp only [chord, z]
    linear_combination (a * chordSlope - f a) * hpq
  let g := fun u : ℝ => f u - chord u
  have hg_a : g a = 0 := by simp [g, hchord_a]
  have hg_b : g b = 0 := by simp [g, hchord_b]
  have hg : ContinuousOn g (Icc a b) :=
    (hf.mono (Icc_subset_Icc ha.1 hb.2)).sub
      (continuous_const.add ((continuous_id.sub continuous_const).mul
        continuous_const)).continuousOn
  change f z < p * f a + q * f b
  rw [← hchord_z]
  by_contra! hbad
  have hz_nonneg : 0 ≤ g z := sub_nonneg.mpr hbad
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨z, Ioo_subset_Icc_self hz⟩ hg
  -- If a maximum is at an endpoint, the interior witness realizes it as well.
  obtain ⟨x, hx, hxmax⟩ : ∃ x ∈ Ioo a b, IsMaxOn g (Icc a b) x := by
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hm with hma | hmb | hm
    · refine ⟨z, hz, isMaxOn_iff.mpr fun u hu => ?_⟩
      exact (isMaxOn_iff.mp hmax u hu).trans (by simpa only [hma, hg_a] using hz_nonneg)
    · refine ⟨z, hz, isMaxOn_iff.mpr fun u hu => ?_⟩
      exact (isMaxOn_iff.mp hmax u hu).trans (by simpa only [hmb, hg_b] using hz_nonneg)
    · exact ⟨m, hm, hmax⟩
  obtain ⟨δ, hδ, hpos⟩ := hcenter x ⟨ha.1.trans_lt hx.1, hx.2.trans_le hb.2⟩
  let radius := min δ (min (x - a) (b - x))
  have hradius : 0 < radius := lt_min hδ (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
  obtain ⟨t, ht, htr⟩ := exists_between hradius
  have htδ : t < δ := htr.trans_le (min_le_left _ _)
  have hta : t < x - a := htr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htb : t < b - x := htr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hplus := isMaxOn_iff.mp hxmax (x + t) ⟨by linarith [hx.1], by linarith⟩
  have hminus := isMaxOn_iff.mp hxmax (x - t) ⟨by linarith, by linarith [hx.2]⟩
  have hcancel : chord (x + t) + chord (x - t) = 2 * chord x := by
    dsimp [chord]
    ring
  dsimp only [g] at hplus hminus
  linarith only [hplus, hminus, hcancel, hpos t ht htδ]

/-- A stationary left endpoint is strictly below the right endpoint. -/
theorem endpoint_lt_of_centered_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (hcenter : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      2 * f x < f (x + t) + f (x - t))
    (hderiv : HasDerivAt f 0 0) : f 0 < f 1 := by
  have hconv := strictConvexOn_of_centered_pos hf hcenter
  have hslope := hconv.lt_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_lt_one hderiv
  simpa only [slope_def_field, sub_zero, div_one, sub_pos] using hslope

/-- A uniform quadratic coefficient gives an endpoint gap even with a local quartic error. -/
theorem endpoint_add_lt_of_centered_quartic {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ContinuousOn f (Icc 0 1))
    (hcenter : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ K : ℝ, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      c * t ^ 2 - K * t ^ 4 ≤ f (x + t) + f (x - t) - 2 * f x)
    (hderiv : HasDerivAt f 0 0) : f 0 + c / 4 < f 1 := by
  let g := fun x : ℝ => f x - c / 4 * x ^ 2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.sub (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hquadDeriv : HasDerivAt (fun x : ℝ => c / 4 * x ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).fun_pow 2).const_mul (c / 4))
  have hgDeriv : HasDerivAt g 0 0 := by simpa [g] using hderiv.fun_sub hquadDeriv
  have hgCenter : ∀ x ∈ Ioo (0 : ℝ) 1, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      2 * g x < g (x + t) + g (x - t) := by
    intro x hx
    obtain ⟨K, δ, hδ, hbound⟩ := hcenter x hx
    have hcont : Continuous (fun t : ℝ => K * t ^ 2) := continuous_const.mul (continuous_id.pow 2)
    have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), K * t ^ 2 < c / 2 :=
      hcont.continuousAt.eventually_lt continuousAt_const (by simpa using half_pos hc)
    obtain ⟨l, u, hu, hlocal⟩ := hsmall.exists_Ioo_subset
    refine ⟨min δ u, lt_min hδ hu.2, fun t ht htu => ?_⟩
    have hKt : K * t ^ 2 < c / 2 :=
      hlocal ⟨hu.1.trans ht, htu.trans_le (min_le_right _ _)⟩
    have herr : K * t ^ 4 < c / 2 * t ^ 2 := by
      rw [show K * t ^ 4 = (K * t ^ 2) * t ^ 2 by ring]
      exact mul_lt_mul_of_pos_right hKt (pow_pos ht 2)
    have hquad : c / 4 * (x + t) ^ 2 + c / 4 * (x - t) ^ 2 - 2 * (c / 4 * x ^ 2) =
        c / 2 * t ^ 2 := by ring
    dsimp only [g]
    linarith only [hbound t ht (htu.trans_le (min_le_left _ _)), herr, hquad]
  have hgap := endpoint_lt_of_centered_pos hg hgCenter hgDeriv
  norm_num [g] at hgap
  linarith only [hgap]

end D5.S3.Quantum.Semigroups.WuCubicCenteredComparison
