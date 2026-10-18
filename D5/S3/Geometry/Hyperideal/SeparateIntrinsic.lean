/- GID: D5/S3/Geometry/Hyperideal/SeparateIntrinsic
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SeparateIntrinsic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Opposite linear support signs separate the intrinsic interiors of two convex sets. -/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.SeparateIntrinsic

abbrev V := Fin 4 → ℝ

private lemma intrinsic_extension (s : Set V) (x y : V)
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ s := by
  obtain ⟨a, ha, hax⟩ := mem_intrinsicInterior.mp hx
  let b : affineSpan ℝ s := ⟨y, subset_affineSpan ℝ s hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  letI : Nonempty (affineSpan ℝ s) := ⟨a⟩
  let v : (affineSpan ℝ s).direction := a -ᵥ b
  let t := ε / (2 * (‖v‖ + 1))
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  have ht : 0 < t := div_pos hε (by positivity)
  have hbound : t * ‖v‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).mpr
    change ε * ‖v‖ < ε * (2 * (‖v‖ + 1))
    nlinarith
  have hm : t • v +ᵥ a ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, dist_vadd_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact hbound
  have hmem := interior_subset (hball hm)
  refine ⟨t, ht, ?_⟩
  change t • ((a : V) - (b : V)) + (a : V) ∈ s at hmem
  simpa only [hax, b, add_comm] using hmem

/-- Opposite support signs keep the intrinsic interiors disjoint. -/
theorem separate_intrinsic (s t : Set V) (L : V →ₗ[ℝ] ℝ)
    (hs : ∀ x ∈ s, L x ≤ 0) (ht : ∀ x ∈ t, 0 ≤ L x)
    (hw : ∃ y ∈ s, L y < 0) :
    Disjoint (intrinsicInterior ℝ s) (intrinsicInterior ℝ t) := by
  rw [Set.disjoint_left]
  intro x hx hxt
  have hxs := intrinsicInterior_subset hx
  have hxts := intrinsicInterior_subset hxt
  have hz : L x = 0 := le_antisymm (hs x hxs) (ht x hxts)
  obtain ⟨y, hy, hly⟩ := hw
  obtain ⟨a, ha, he⟩ := intrinsic_extension s x y hx hy
  have hn := hs _ he
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hz, zero_sub, zero_add] at hn
  exact (not_lt_of_ge hn) (mul_pos ha (neg_pos.mpr hly))

#print axioms separate_intrinsic

end D5.S3.Geometry.Hyperideal.SeparateIntrinsic
