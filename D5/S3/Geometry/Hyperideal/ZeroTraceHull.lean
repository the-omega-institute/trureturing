/- GID: D5/S3/Geometry/Hyperideal/ZeroTraceHull
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ZeroTraceHull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Hull]
   utility: none
   digest: A finite convex hull meets a family of nonpositive supports at the hull of its zero-support vertices. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.ZeroTraceHull

abbrev V := Fin 4 → ℝ

/-- If every generator lies in every support halfspace, the common zero trace
is exactly the convex hull of the generators on that trace. -/
theorem zero_trace_hull {I : Type*} (s : Set V) (L : I → V →ₗ[ℝ] ℝ)
    (hs : ∀ p ∈ s, ∀ i, L i p ≤ 0) :
    convexHull ℝ {p ∈ s | ∀ i, L i p = 0} =
      {x ∈ convexHull ℝ s | ∀ i, L i x = 0} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · exact fun p hp => ⟨subset_convexHull ℝ s hp.1, hp.2⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ s) hx.1 hy.1 ha hb hab, ?_⟩
      intro i
      simp [map_add, map_smul, hx.2 i, hy.2 i]
  · rintro x ⟨hx, hzero⟩
    obtain ⟨J, _, w, z, hw, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hx
    have hterm (i : I) (j : J) : w j * L i (z j) = 0 := by
      have hh : ∑ j, w j * L i (z j) = 0 := by
        simpa only [map_sum, map_smul, smul_eq_mul, hzero i] using congrArg (L i) he
      exact (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw j) (hs (z j) (hz j) i))).mp hh
          j (Finset.mem_univ j)
    let t : Finset J := Finset.univ.filter fun j => w j ≠ 0
    have ht_sum : ∑ j ∈ t, w j = 1 := by
      rw [show (∑ j ∈ t, w j) = ∑ j, w j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        by_contra hjw
        exact hjt (Finset.mem_filter.mpr ⟨hj, hjw⟩)]
      exact hsum
    have ht_vec : ∑ j ∈ t, w j • z j = x := by
      rw [show (∑ j ∈ t, w j • z j) = ∑ j, w j • z j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        have hjw : w j = 0 := by
          by_contra hn
          exact hjt (Finset.mem_filter.mpr ⟨hj, hn⟩)
        simp [hjw]]
      exact he
    rw [← ht_vec]
    exact (convex_convexHull ℝ _).sum_mem
      (fun j _ => hw j) ht_sum (fun j hj => subset_convexHull ℝ _
        ⟨hz j, fun i => (mul_eq_zero.mp (hterm i j)).resolve_left
          (Finset.mem_filter.mp hj).2⟩)

#print axioms zero_trace_hull

end D5.S3.Geometry.Hyperideal.ZeroTraceHull
