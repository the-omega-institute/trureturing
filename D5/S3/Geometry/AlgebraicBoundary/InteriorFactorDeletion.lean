/- GID: D5/S3/Geometry/AlgebraicBoundary/InteriorFactorDeletion
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/InteriorFactorDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Linear factors through interior points can be deleted on entire convex boundaries. -/

import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! A boundary equation cannot require a hyperplane passing through a convex interior point. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem centered_factor_delete {B : Set E} (hB : Convex ℝ B)
    (h0 : B ∈ 𝓝 (0 : E)) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    {g : E → ℝ} (hg : Continuous g)
    (hvan : ∀ x ∈ frontier B, L x * g x = 0) :
    ∀ x ∈ frontier B, g x = 0 := by
  intro b hb
  by_cases hLb : L b = 0
  · have hv : ∃ v : E, L v ≠ 0 := by
      by_contra! h
      apply hL
      ext x
      exact h x
    obtain ⟨v, hv⟩ := hv
    have hgb : gauge B b = 1 := (gauge_eq_one_iff_mem_frontier hB h0).2 hb
    let y : ℝ → E := fun t => b + t • v
    let z : ℝ → E := fun t => (gauge B (y t))⁻¹ • y t
    have hy : Continuous y := continuous_const.add (continuous_id.smul continuous_const)
    have hgy : Continuous (fun t => gauge B (y t)) := (continuous_gauge hB h0).comp hy
    have hgy0 : gauge B (y 0) = 1 := by simpa [y] using hgb
    have hz0 : z 0 = b := by simp [z, y, hgb]
    have hzt : Tendsto z (𝓝 (0 : ℝ)) (𝓝 b) := by
      rw [← hz0]
      exact ((hgy.continuousAt.inv₀ (by rw [hgy0]; norm_num)).smul hy.continuousAt)
    have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < gauge B (y t) :=
      hgy.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < gauge B (y 0) by
        rw [hgy0]; norm_num))
    have hzero : ∀ᶠ t in 𝓝[≠] (0 : ℝ), g (z t) = 0 := by
      filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htn
      have ht0 : t ≠ 0 := htn
      have hzb : z t ∈ frontier B := by
        apply (gauge_eq_one_iff_mem_frontier hB h0).1
        simp only [z, gauge_smul_of_nonneg (inv_nonneg.mpr ht.le), smul_eq_mul]
        exact inv_mul_cancel₀ ht.ne'
      have hLz : L (z t) ≠ 0 := by
        simp only [z, map_smul, smul_eq_mul, y, map_add, hLb, zero_add]
        exact mul_ne_zero (inv_ne_zero ht.ne') (mul_ne_zero ht0 hv)
      exact (mul_eq_zero.mp (hvan (z t) hzb)).resolve_left hLz
    have htend : Tendsto (fun t => g (z t)) (𝓝[≠] (0 : ℝ)) (𝓝 (g b)) :=
      (hg.continuousAt.tendsto.comp hzt).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique htend
      (tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm)))
  · exact (mul_eq_zero.mp (hvan b hb)).resolve_left hLb

/-- Let a convex set contain `a` in its interior. If a continuous function
multiplied by a nonzero linear factor through `a` vanishes on the entire
boundary, the continuous function itself vanishes on the entire boundary.
No differentiability or strict convexity of the boundary is required. -/
theorem whole_boundary_factor_delete {B : Set E} (hB : Convex ℝ B)
    {a : E} (ha : a ∈ interior B) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    {g : E → ℝ} (hg : Continuous g)
    (hvan : ∀ x ∈ frontier B, L (x - a) * g x = 0) :
    ∀ x ∈ frontier B, g x = 0 := by
  let A : Set E := (fun x => a + x) ⁻¹' B
  have hA : Convex ℝ A := hB.translate_preimage_right a
  have hA0 : A ∈ 𝓝 (0 : E) := by
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.mp ha)
  have hfront : ∀ x, x ∈ frontier A ↔ a + x ∈ frontier B := by
    intro x
    exact Set.ext_iff.mp ((Homeomorph.addLeft a).preimage_frontier B).symm x
  have hdel := centered_factor_delete hA hA0 L hL
    (hg.comp (continuous_const.add continuous_id)) (by
      intro x hx
      simpa only [Function.comp_apply, Pi.add_apply, id_eq, add_sub_cancel_left]
        using hvan (a + x) ((hfront x).mp hx))
  intro x hx
  have hxa : x - a ∈ frontier A := (hfront (x - a)).mpr (by simpa using hx)
  simpa using hdel (x - a) hxa

#print axioms whole_boundary_factor_delete

end D5.S3.Geometry.AlgebraicBoundary.InteriorFactorDeletion
