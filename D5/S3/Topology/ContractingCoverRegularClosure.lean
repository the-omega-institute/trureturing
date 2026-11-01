/- GID: D5/S3/Topology/ContractingCoverRegularClosure
   generality: G
   mirror-B: D5/B/S3/Topology/ContractingCoverRegularClosure
   mirror-E: none(waiver:unbounded-metric-inference)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.HausdorffDistance]
   utility: none
   digest: A compact set covered by uniformly contracting open branches is the closure of its nonempty interior. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Maps.Basic
import Mathlib.Tactic.Linarith

namespace D5.S3.Topology.ContractingCoverRegularClosure

open Set Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A nonempty closed forward invariant core exhausts a compact set with
contracting preimages. The nonemptiness is essential for real-valued infDist. -/
private theorem invariant_core_eq {X I : Type*} [MetricSpace X]
    {K C : Set X} (hK : IsCompact K) (hC : IsClosed C)
    (hne : C.Nonempty) (hsub : C ⊆ K)
    {q : NNReal} (hq : q < 1) (f : I → X → X)
    (hlip : ∀ i, LipschitzWith q (f i))
    (hcover : ∀ x ∈ K, ∃ i, ∃ y ∈ K, f i y = x)
    (hmap : ∀ i, MapsTo (f i) C C) : C = K := by
  have hCc : IsCompact C := hK.of_isClosed_subset hC hsub
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn (hne.mono hsub)
    (continuous_infDist_pt C).continuousOn
  obtain ⟨i, y, hy, rfl⟩ := hcover x hx
  obtain ⟨c, hc, hdist⟩ := hCc.exists_infDist_eq_dist hne y
  have hstep : infDist (f i y) C ≤ (q : ℝ) * infDist (f i y) C := by
    calc
      infDist (f i y) C ≤ dist (f i y) (f i c) :=
        infDist_le_dist_of_mem (hmap i hc)
      _ ≤ (q : ℝ) * dist y c := (hlip i).dist_le_mul y c
      _ = (q : ℝ) * infDist y C := by rw [hdist]
      _ ≤ (q : ℝ) * infDist (f i y) C :=
        mul_le_mul_of_nonneg_left (hmax hy) q.coe_nonneg
  have hq' : (q : ℝ) < 1 := hq
  have hzero : infDist (f i y) C = 0 := by
    have hn := infDist_nonneg (x := f i y) (s := C)
    nlinarith
  apply Subset.antisymm hsub
  intro t ht
  apply (hC.mem_iff_infDist_zero hne).2
  exact le_antisymm ((hmax ht).trans_eq hzero) infDist_nonneg

/-- No finiteness of the branch index, ambient completeness, or properness is
needed: compactness, a common strict contraction, an exact self-cover and open
branches propagate one open patch throughout the compact carrier. -/
theorem closure_interior_eq_of_contracting_cover
    {X I : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (hne : (interior K).Nonempty)
    {q : NNReal} (hq : q < 1) (f : I → X → X)
    (hlip : ∀ i, LipschitzWith q (f i))
    (hopen : ∀ i, IsOpenMap (f i))
    (hcover : (⋃ i, f i '' K) = K) : closure (interior K) = K := by
  have hmap : ∀ i, MapsTo (f i) K K := by
    intro i x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  apply invariant_core_eq hK isClosed_closure hne.closure
    (closure_minimal interior_subset hK.isClosed) hq f hlip
  · intro x hx
    rw [← hcover] at hx
    obtain ⟨i, y, hy, he⟩ := mem_iUnion.mp hx
    exact ⟨i, y, hy, he⟩
  · intro i x hx
    exact closure_mono ((hopen i).mapsTo_interior (hmap i)).image_subset
      (image_closure_subset_closure_image (hlip i).continuous ⟨x, hx, rfl⟩)

end D5.S3.Topology.ContractingCoverRegularClosure
