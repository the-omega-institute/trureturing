/- GID: D5/S3/Combinatorics/Graph/Walks/ActualTwoOrderStateTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualTwoOrderStateTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Map One Cycle and Both Marked Orders Together. -/
import D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
import D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualTwoOrderStateTransport

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {J : SimpleGraph W}

/-- Include a whole simultaneous state in a larger graph, or identify its
native domain by an injective graph map. Every output piece is the literal
image of its source piece on the same mapped cycle. -/
theorem actual_two_order_state_map (f : G →g J) (hf : Function.Injective f)
    {base : V} (w : G.Walk base base) (K H : Finset (Sym2 V))
    (joint primary opposite : List (Piece G))
    (hs : ActualTwoOrderPartitions w K H joint primary opposite) :
    ActualTwoOrderPartitions (w.map f) (K.image (Sym2.map f)) (H.image (Sym2.map f))
      (joint.map (mapPiece f)) (primary.map (mapPiece f)) (opposite.map (mapPiece f)) := by
  classical
  obtain ⟨hcycle, _, hjs, hje, hjc⟩ :=
    actual_cycle_partition_map f hf w hs.cycle joint (K ∪ H)
      hs.joint_partition.support hs.joint_partition.edges hs.joint_partition.cut_mem
  obtain ⟨_, _, hps, hpe, hpc⟩ :=
    actual_cycle_partition_map f hf w hs.cycle primary K
      hs.primary_partition.support hs.primary_partition.edges hs.primary_partition.cut_mem
  obtain ⟨_, _, hos, hoe, hoc⟩ :=
    actual_cycle_partition_map f hf w hs.cycle opposite H
      hs.opposite_partition.support hs.opposite_partition.edges hs.opposite_partition.cut_mem
  have heinj : Function.Injective (Sym2.map f) := Sym2.map.injective hf
  have hd : Disjoint (K.image (Sym2.map f)) (H.image (Sym2.map f)) := by
    apply Finset.disjoint_left.mpr
    intro e heK heH
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp heK
    obtain ⟨h, hh, hhe⟩ := Finset.mem_image.mp heH
    exact Finset.disjoint_left.mp hs.disjoint hk ((heinj (hke.trans hhe.symm)).symm ▸ hh)
  rw [Finset.image_union] at hje hjc
  exact ⟨hcycle, hd, ⟨hjs, hje, hjc⟩, ⟨hps, hpe, hpc⟩, ⟨hos, hoe, hoc⟩⟩

#print axioms actual_two_order_state_map

end D5.S3.Combinatorics.Graph.Walks.ActualTwoOrderStateTransport
