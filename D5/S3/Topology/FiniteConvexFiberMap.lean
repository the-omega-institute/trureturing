/- GID: D5/S3/Topology/FiniteConvexFiberMap
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteConvexFiberMap
   mirror-E: none(waiver:abstract-topological-construction)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.PartitionOfUnity]
   utility: none
   digest: Finite convex averaging controls entire fibers and avoids a forbidden set. -/

import D5.S3.Topology.FiniteCenteredStarRefinement
import Mathlib.Analysis.Convex.PartitionOfUnity

/-! Finite averaging of discontinuous fiber representatives with common convex control. -/

set_option autoImplicit false

open Set Topology
open scoped BigOperators

noncomputable section

namespace D5.S3.Topology.FiniteConvexFiberMap

/-- Convex neighborhoods controlling entire fibers produce a continuous map avoiding
a forbidden set. The exceptional neighborhoods are handled by a convex slice, and
every fiber point can be joined to the map value without passing through zero.
The representatives `a` need not be continuous. -/
theorem exists_continuous_ray_avoiding_fiber_map
    {X E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (V : Fin n → Set X) (hVo : ∀ j, IsOpen (V j))
    (hVc : ∀ x, ∃ j, x ∈ V j)
    (B : X → Set E) (N : Fin n → Set E) (K L R : Set E) (O : Set X)
    (hK : Convex ℝ K) (hL : Convex ℝ L) (hN : ∀ j, Convex ℝ (N j))
    (hBK : ∀ x, B x ⊆ K)
    (hVN : ∀ j x, x ∈ V j → B x ⊆ N j)
    (hNzero : ∀ j, (0 : E) ∉ N j)
    (hNR : ∀ j, Disjoint (N j) R ∨ V j ⊆ O)
    (hLR : L ∩ R ⊆ {0})
    (a : X → E) (ha : ∀ x, a x ∈ B x) (haL : ∀ x ∈ O, a x ∈ L) :
    ∃ A : C(X, E),
      (∀ x, A x ∈ K) ∧ (∀ x, A x ∉ R) ∧
      ∀ x b, b ∈ B x → (0 : E) ∉ segment ℝ b (A x) := by
  classical
  obtain ⟨U, s, hUo, hUc, hcover, hstar⟩ :=
    FiniteCenteredStarRefinement.exists_finite_centered_star_refinement V hVo hVc
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun c : s => U c) (fun c => hUo c)
    (by intro x _; obtain ⟨c, hc, hx⟩ := hcover x
        exact mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩)
  have hsupport : ∀ (c : s) x, φ c x ≠ 0 → x ∈ U c := by
    intro c x hx
    exact hφ c (subset_closure hx)
  let A : C(X, E) := ⟨fun x => ∑ c : s, φ c x • a c,
    continuous_finsetSum _ fun c _ => (φ c).continuous.smul continuous_const⟩
  have hmem : ∀ (T : Set E), Convex ℝ T → ∀ x,
      (∀ c : s, φ c x ≠ 0 → a c ∈ T) → A x ∈ T := by
    intro T hT x hx
    simpa only [A, ContinuousMap.coe_mk, finsum_eq_sum_of_fintype] using
      φ.finsum_smul_mem_convex (mem_univ x) hx hT
  have hcontrol : ∀ x, ∃ j, B x ⊆ N j ∧ A x ∈ N j ∧
      (∀ c : s, φ c x ≠ 0 → (c : X) ∈ V j) := by
    intro x
    obtain ⟨c, hc⟩ := φ.exists_pos (mem_univ x)
    have hxc := hsupport c x hc.ne'
    obtain ⟨j, hj⟩ := hstar c c.property
    have hxj : x ∈ V j := hj c c.property ⟨x, hxc, hxc⟩ hxc
    have hcenters : ∀ d : s, φ d x ≠ 0 → (d : X) ∈ V j := by
      intro d hd
      exact hj d d.property ⟨x, hxc, hsupport d x hd⟩ (hUc d)
    refine ⟨j, hVN j x hxj, hmem (N j) (hN j) x ?_, hcenters⟩
    intro d hd
    exact hVN j d (hcenters d hd) (ha d)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x
    exact hmem K hK x fun c _ => hBK c (ha c)
  · intro x hxR
    obtain ⟨j, hBx, hAx, hcenters⟩ := hcontrol x
    rcases hNR j with hj | hj
    · exact (Set.disjoint_left.mp hj) hAx hxR
    · have hAxL : A x ∈ L := hmem L hL x fun c hc => haL c (hj (hcenters c hc))
      have hzero : A x = 0 := hLR ⟨hAxL, hxR⟩
      exact hNzero j (hzero ▸ hAx)
  · intro x b hb hz
    obtain ⟨j, hBx, hAx, _⟩ := hcontrol x
    exact hNzero j ((hN j).segment_subset (hBx hb) hAx hz)

end D5.S3.Topology.FiniteConvexFiberMap
