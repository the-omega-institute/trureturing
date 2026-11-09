/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodParameters
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [D5/S3/Combinatorics/Graph/StarForming/CubicCertificate, D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim; result=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result; claim=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim
   digest: The original Heawood graph has beta two seven and upper two-star formation eight. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicCertificate
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity

/-! The original cyclic labels, incidence rows and selected eight-set are reused
from the supplier. The finite mask cap is only for this fourteen-vertex graph;
it is not a finite substitute for any unbounded composition or cover theorem. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
open StarFormingDissociationRefutation Cubic

def graph : SimpleGraph (Fin 14) where
  Adj := FanoAdj
  symm := ⟨fun a b h => (fano_simple_cubic.2.1 a b).mp h⟩
  loopless := ⟨fano_simple_cubic.1⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (b ∈ fanoNeighbors a))

def selectedSet : Finset (Fin 14) := Finset.univ.filter fanoSelected

def maskSet (mask : Fin 16384) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => mask.val.testBit v.val = true)

def maskDissociates (mask : Fin 16384) : Prop :=
  ∀ v : Fin 14, mask.val.testBit v.val = true →
    ((fanoNeighbors v).filter (fun w => mask.val.testBit w.val)).length ≤ 1

/-- The supplier's sparse neighbor lists count actual canonical selected degrees. -/
theorem mask_dissociation_iff (mask : Fin 16384) :
    maskDissociates mask ↔ IsKIndependent graph 2 (maskSet mask) := by
  have hc (v : Fin 14) :
      ((fanoNeighbors v).filter (fun w => mask.val.testBit w.val)).length =
        ((maskSet mask).filter (graph.Adj v)).card := by
    rw [← List.toFinset_card_of_nodup ((fano_simple_cubic.2.2 v).2.filter _)]
    congr 1
    ext w
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,maskSet,
      Finset.mem_univ,true_and]
    change (w ∈ fanoNeighbors v ∧ mask.val.testBit w.val = true) ↔
      (mask.val.testBit w.val = true ∧ w ∈ fanoNeighbors v)
    exact and_comm
  constructor
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc] at hh
    omega
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc]
    omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- Exact finite cap for all subsets of this fixed Fano incidence graph. -/
theorem mask_cap : ∀ mask : Fin 16384, maskDissociates mask →
    ((List.finRange 14).filter (fun v => mask.val.testBit v.val)).length ≤ 7 := by
  unfold maskDissociates fanoNeighbors
  decide +kernel

/-- Both the upper bound and an actual bipartition side are checked. -/
theorem beta_graph : beta graph 2 = 7 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask S
    have he : maskSet mask = S := by ext v; simp [maskSet,hm]
    have hi : maskDissociates mask := (mask_dissociation_iff mask).mpr
      (he.symm ▸ (Finset.mem_filter.mp hS).2)
    have hc := mask_cap mask hi
    rw [FiniteMasks.list_count] at hc
    change (maskSet mask).card ≤ 7 at hc
    simpa only [he] using hc
  · let S : Finset (Fin 14) := {0,1,2,3,4,5,6}
    have hi : IsKIndependent graph 2 S := by
      change IsKIndependent graph 2 {0,1,2,3,4,5,6}
      unfold IsKIndependent graph FanoAdj fanoNeighbors
      decide +kernel
    have hc : S.card = 7 := by decide +kernel
    rw [← hc]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

/-- Degree capacity supplies the all-minimal-selection upper bound. -/
theorem sf_graph : SF graph 2 = 8 := by
  classical
  have hd : ∀ v : Fin 14, DegreeCapacity.degree graph v = 3 := by
    unfold DegreeCapacity.degree graph FanoAdj fanoNeighbors
    decide +kernel
  have hu := DegreeCapacity.sf_regular_bound graph 3 (by omega) hd
  have hm : IsMinimalStarForming graph 2 selectedSet := by
    apply (regular_minimal_iff graph selectedSet).mp
    simpa [graph,selectedSet] using fano_minimal
  have hc : selectedSet.card = 8 := by
    have hh := fano_selected_card
    rw [FiniteMasks.list_count] at hh
    simpa [selectedSet] using hh
  have hl : selectedSet.card ≤ SF graph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hm⟩)
  rw [hc] at hl
  norm_num at hu
  omega

/-- The graph is bipartite and every vertex has degree three. -/
theorem graph_class : graph.Colorable 2 ∧
    ∀ v, (Finset.univ.filter (graph.Adj v)).card = 3 := by
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 7 then (0 : Fin 2) else 1) ?_⟩
    change ∀ a b : Fin 14, FanoAdj a b →
      (if a.val < 7 then (0 : Fin 2) else 1) ≠ (if b.val < 7 then 0 else 1)
    unfold FanoAdj fanoNeighbors
    decide +kernel
  · unfold graph FanoAdj fanoNeighbors
    decide +kernel

/-- The original universal cubic bipartite identification is false. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.Colorable 2 → (∀ v, (Finset.univ.filter (G.Adj v)).card = 3) → beta G 2 = SF G 2

theorem result : ¬ claim := by
  intro h
  have hh := h 14 graph graph_class.1 graph_class.2
  rw [beta_graph,sf_graph] at hh
  omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
