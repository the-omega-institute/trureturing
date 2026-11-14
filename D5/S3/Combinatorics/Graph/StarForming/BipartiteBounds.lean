/- GID: D5/S3/Combinatorics/Graph/StarForming/BipartiteBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BipartiteBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Bipartition sides give the actual half-order dissociation lower bound. -/

import D5.S3.Combinatorics.Graph.StarForming.Comparison

namespace D5.S3.Combinatorics.Graph.StarForming.BipartiteBounds
open StarFormingDissociationRefutation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any independent color class is a canonical dissociation selection. -/
theorem color_class_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.Coloring (Fin 2)) (i : Fin 2) :
    IsKIndependent G 2 (Finset.univ.filter (fun v => c v = i)) := by
  classical
  intro v hv
  have hc := (Finset.mem_filter.mp hv).2
  have he : ((Finset.univ.filter (fun w => c w = i)).filter (G.Adj v)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw hedge
    exact c.valid hedge (hc.trans (Finset.mem_filter.mp hw).2.symm)
  rw [he]
  simp

/-- No regularity, connectedness or nonempty assumption is needed. -/
theorem card_le_two_beta (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) : Fintype.card V ≤ 2 * beta G 2 := by
  classical
  obtain ⟨c⟩ := hG
  let L := Finset.univ.filter (fun v => c v = (0 : Fin 2))
  let R := Finset.univ.filter (fun v => c v = (1 : Fin 2))
  have hL : L.card ≤ beta G 2 := Finset.le_sup (Finset.mem_filter.mpr
    ⟨by simp,color_class_independent G c 0⟩)
  have hR : R.card ≤ beta G 2 := Finset.le_sup (Finset.mem_filter.mpr
    ⟨by simp,color_class_independent G c 1⟩)
  have hu : L ∪ R = Finset.univ := by
    ext v
    have hh : c v = 0 ∨ c v = 1 := by omega
    simp [L,R,hh]
  have hd : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have ha := (Finset.mem_filter.mp hv).2
    have hb := (Finset.mem_filter.mp hw).2
    have he : (0 : Fin 2) = 1 := ha.symm.trans hb
    exact (by decide : (0 : Fin 2) ≠ 1) he
  have hc := Finset.card_union_of_disjoint hd
  rw [hu,Finset.card_univ] at hc
  omega

end D5.S3.Combinatorics.Graph.StarForming.BipartiteBounds
