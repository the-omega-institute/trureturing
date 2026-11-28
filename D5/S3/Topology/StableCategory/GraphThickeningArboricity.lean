/- GID: D5/S3/Topology/StableCategory/GraphThickeningArboricity
   generality: G
   mirror-B: none(waiver:consumed-by-graph-thickening-forest-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The graph thickening satisfies the ambient cycle rigidity conditions. -/

import D5.S3.Topology.StableCategory.GraphCycleCategoricalObstruction
import D5.S3.Topology.StableCategory.GraphThickeningStableCover

/-! Graph cycles give an ordinary categorical lower-cover obstruction for the graph thickening. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Topology.StableCategory.GraphThickeningArboricity

open D5.S3.Topology.ConnectedCategoryGraft (HasCategoricalCover)
open D5.S3.Topology.GraphCycleCategoricalObstruction (GraphPosetLabels edgeOfAdj arboricity)
open D5.S3.Topology.StableCategory.GraphThickeningStableCover
  (Edge Vertex original endpoint endpoint_pair cap newMaximum newMaximum_isMax
    pathFace side lt_newMaximum_iff IsConeFace IsSubdividedFace P_G)
open scoped Classical

variable {V : Type*} (G : SimpleGraph V)

private def vertexLabel (v : V) : P_G G :=
  ⟨{original G v}, Finset.singleton_nonempty _, Or.inl
    (Or.inr (Or.inl ⟨v, Finset.erase_subset _ _⟩))⟩

private theorem original_mem_cap (v : V) (e : Edge G) :
    original G v ∈ cap G e ↔ v ∈ e.val := by
  conv_rhs => rw [← endpoint_pair G e]
  simp [cap, original, GraphThickeningStableCover.midpoint, Sym2.mem_iff]

private theorem eq_of_mem_caps {v : V} {e f : Edge G} (hef : e ≠ f)
    (he : v ∈ e.val) (hf : v ∈ f.val) {a : Vertex G}
    (hae : a ∈ cap G e) (haf : a ∈ cap G f) : a = original G v := by
  cases a with
  | none => simp [cap, original, GraphThickeningStableCover.midpoint] at hae
  | some a =>
    cases a with
    | inl w =>
      have hwe := (original_mem_cap G w e).mp hae
      have hwf := (original_mem_cap G w f).mp haf
      by_cases hw : w = v
      · exact congrArg (original G) hw
      · exact (hef (Subtype.ext (Sym2.eq_of_ne_mem hw hwe he hwf hf))).elim
    | inr q =>
      have hqe : q = e := by simpa [cap, original, GraphThickeningStableCover.midpoint] using hae
      have hqf : q = f := by simpa [cap, original, GraphThickeningStableCover.midpoint] using haf
      exact (hef (hqe.symm.trans hqf)).elim

/-- The original vertices and the new maxima in the graph thickening
satisfy the two ambient rigidity conditions for cycles. -/
def labels : GraphPosetLabels G (P_G G) where
  vertex := vertexLabel G
  vertex_injective := by
    intro u v h
    have hval := congrArg Subtype.val h
    simpa [vertexLabel, original] using hval
  vertex_min := by
    intro v x hx
    change x.val ⊆ {original G v} at hx
    have he : x.val = {original G v} :=
      Finset.Subset.antisymm hx (by
        obtain ⟨a, ha⟩ := x.property.1
        exact Finset.singleton_subset_iff.mpr (Finset.mem_singleton.mp (hx ha) ▸ ha))
    exact (Subtype.ext he : x = vertexLabel G v).ge
  edgeTop := newMaximum G
  edge_max := newMaximum_isMax G
  vertex_le_edge := by
    intro v e hv
    exact Finset.singleton_subset_iff.mpr ((original_mem_cap G v e).mpr hv)
  incident_rigid := by
    intro v e f x hef he hf hv hxe hxf
    apply Subtype.ext
    change x.val = {original G v}
    exact Finset.Subset.antisymm
      (fun _ ha => Finset.mem_singleton.mpr (eq_of_mem_caps G hef he hf (hxe ha) (hxf ha))) hv
  endpoints_rigid := by
    intro u v h x hu hv hx
    by_contra hne
    obtain ⟨i, hi⟩ := (lt_newMaximum_iff G x (edgeOfAdj h)).mp (lt_of_le_of_ne hx hne)
    have huu : original G u ∈ side G (edgeOfAdj h) i :=
      hi (hu (Finset.mem_singleton_self _))
    have hvv : original G v ∈ side G (edgeOfAdj h) i :=
      hi (hv (Finset.mem_singleton_self _))
    have hue : u = endpoint G (edgeOfAdj h) i := by
      simpa [side, original, GraphThickeningStableCover.midpoint] using huu
    have hve : v = endpoint G (edgeOfAdj h) i := by
      simpa [side, original, GraphThickeningStableCover.midpoint] using hvv
    exact h.ne (hue.trans hve.symm)

/-- A categorical lower cover of a graph thickening uses at least as
many sets as are needed to cover the graph by forests. -/
theorem arboricity_le_of_hasCategoricalCover [Finite V] {n : ℕ}
    (h : HasCategoricalCover (P_G G) n) : arboricity G ≤ n :=
  Nat.sInf_le ((labels G).hasForestCover_of_hasCategoricalCover h)

end D5.S3.Topology.StableCategory.GraphThickeningArboricity
