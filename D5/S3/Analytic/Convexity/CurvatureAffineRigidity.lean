/- GID: D5/S3/Analytic/Convexity/CurvatureAffineRigidity
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/CurvatureAffineRigidity
   mirror-E: none(waiver:local-slope-proof)
   anchors: []
   utility: none
   digest: Affine rigidity forces full support of the actual convex Stieltjes curvature. -/
import D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Convex secant slopes connect local affine rigidity to actual curvature support. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Analytic.Convexity.CurvatureAffineRigidity

open Set Filter MeasureTheory
open scoped Topology
open CurvatureHingeRepresentation

private lemma affine_segment_of_rightDeriv_eq {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (he : rightDeriv f a = rightDeriv f b) :
    ∀ x ∈ Ioo a b, f x = rightDeriv f a * x + (f a - rightDeriv f a * a) := by
  intro x hx
  have hi (y : ℝ) (hy : 0 < y) : y ∈ interior (Ioi (0 : ℝ)) := by
    simpa only [interior_Ioi, mem_Ioi] using hy
  have hx0 : 0 < x := ha.trans hx.1
  have hlo := hf.rightDeriv_le_slope_of_mem_interior (hi a ha) hx0 hx.1
  have hhi := (hf.slope_le_leftDeriv_of_mem_interior ha (hi x hx0) hx.1).trans
    (hf.leftDeriv_le_rightDeriv_of_mem_interior (hi x hx0))
  have hm := hf.monotoneOn_rightDeriv (hi x hx0) (hi b (ha.trans hab)) hx.2.le
  change rightDeriv f x ≤ rightDeriv f b at hm
  change rightDeriv f a ≤ slope f a x at hlo
  change slope f a x ≤ rightDeriv f x at hhi
  have hs : slope f a x = rightDeriv f a := le_antisymm
    (hhi.trans (hm.trans he.symm.le)) hlo
  rw [slope_def_field] at hs
  have hs' := (div_eq_iff (sub_ne_zero.mpr hx.1.ne')).mp hs
  nlinarith

/-- A convex function with local-to-global affine rigidity and no global affine
representation has full Stieltjes curvature support on the positive subtype.
The rigidity premise is supplied by actual two-dimensional operator convexity
in `OperatorConvexCurvature`; it is not a curvature or strict-convexity premise. -/
theorem full_support_of_affine_rigidity {f : ℝ → ℝ}
    (hf : ConvexOn ℝ (Ioi 0) f)
    (rigidity : ∀ (a b α β : ℝ), 0 < a → a < b →
      (∀ x ∈ Ioo a b, f x = α * x + β) →
      ∀ x ∈ Ioi 0, f x = α * x + β)
    (nonaffine : ¬ ∃ α β : ℝ, ∀ x ∈ Ioi 0, f x = α * x + β) :
    (curvature hf).support = univ := by
  have hstrict : StrictMonoOn (rightDeriv f) (Ioi 0) := by
    intro a ha b hb hab
    have hm := hf.monotoneOn_rightDeriv
      (by simpa only [interior_Ioi] using ha)
      (by simpa only [interior_Ioi] using hb) hab.le
    change rightDeriv f a ≤ rightDeriv f b at hm
    refine lt_of_le_of_ne hm ?_
    intro he
    exact nonaffine ⟨rightDeriv f a, f a - rightDeriv f a * a,
      rigidity a b _ _ ha hab (affine_segment_of_rightDeriv_eq hf ha hab he)⟩
  have hmass (a b : Positive) (hab : a < b) : 0 < curvature hf (Ioc a b) := by
    rw [curvature_Ioc, ENNReal.ofReal_pos]
    exact sub_pos.mpr (hstrict a.property b.property hab)
  apply eq_univ_of_forall
  intro x
  apply (Measure.mem_support_iff_forall x).2
  intro U hU
  obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hU
  obtain ⟨v, hxv, hvb⟩ := exists_between hxb
  exact (hmass a v (hax.trans hxv)).trans_le (measure_mono (fun y hy =>
    hsub ⟨hy.1, hy.2.trans_lt hvb⟩))

#print axioms full_support_of_affine_rigidity

end D5.S3.Analytic.Convexity.CurvatureAffineRigidity
