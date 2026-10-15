/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve Actual Native Partitions Under Identity Maps. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
import D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateTransport

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open private mapped_supports mapped_edges from
  D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport

/-- An inclusion that keeps each actual configuration carries both
joint and half-restored states without changing raw inventories. The
source cycle may occupy only a proper child of the target native graph. -/
theorem native_actual_identity_partition_transport {m : ℕ}
    (U V : Configuration m → Prop) (f : domainGraph U →g domainGraph V)
    (hval : ∀ x, (f x).val = x.val)
    {base : {x : Configuration m // U x}}
    (w : (domainGraph U).Walk base base) (hw : w.IsCycle)
    (pieces : List (Piece (domainGraph U)))
    (cuts : Finset (Sym2 {x : Configuration m // U x}))
    (hsupport : (pieces.flatMap fun p => p.walk.support).Perm w.support.tail)
    (hedges : (pieces.flatMap fun p => p.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ cuts)))
    (hcuts : ∀ e ∈ cuts, e ∈ w.edges) :
    let mapped := pieces.map (mapPiece f)
    (w.map f).IsCycle ∧
      (∀ p ∈ mapped, p.walk.IsPath) ∧
      (mapped.flatMap fun p => p.walk.support).Perm (w.map f).support.tail ∧
      (mapped.flatMap fun p => p.walk.edges).Perm
        ((w.map f).edges.filter fun e => decide (e ∉ cuts.image (Sym2.map f))) ∧
      (∀ e ∈ cuts.image (Sym2.map f), e ∈ (w.map f).edges) ∧
      (w.map f).support.map Subtype.val = w.support.map Subtype.val ∧
      (w.map f).edges.map (Sym2.map Subtype.val) = w.edges.map (Sym2.map Subtype.val) ∧
      ((mapped.flatMap fun p => p.walk.support).map Subtype.val) =
        (pieces.flatMap fun p => p.walk.support).map Subtype.val ∧
      ((mapped.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val)) =
        (pieces.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val) ∧
      (cuts.image (Sym2.map f)).image (Sym2.map Subtype.val) =
        cuts.image (Sym2.map Subtype.val) ∧
      (∀ p, (mapPiece f p).start.val = p.start.val ∧
        (mapPiece f p).finish.val = p.finish.val) := by
  classical
  dsimp only
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (hval x).symm.trans ((congrArg Subtype.val h).trans (hval y))
  obtain ⟨hcycle, hpaths, hs, he, hretained⟩ :=
    actual_cycle_partition_map f hf w hw pieces cuts hsupport hedges hcuts
  have hfun : Subtype.val ∘ f = (Subtype.val : {x : Configuration m // U x} → Configuration m) :=
    funext hval
  have hedgefun : Sym2.map Subtype.val ∘ Sym2.map f =
      (Sym2.map Subtype.val : Sym2 {x : Configuration m // U x} → Sym2 (Configuration m)) := by
    funext e
    rw [Function.comp_apply, Sym2.map_map, hfun]
  refine ⟨hcycle, hpaths, hs, he, hretained, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map, List.map_map, hfun]
  · rw [SimpleGraph.Walk.edges_map, List.map_map, hedgefun]
  · rw [mapped_supports, List.map_map, hfun]
  · rw [mapped_edges, List.map_map, hedgefun]
  · rw [Finset.image_image, hedgefun]
  · intro p
    exact ⟨hval p.start, hval p.finish⟩

/-- The actual current parent state is an actual next marked state on
the same mapped cycle. Its complete count law is earned from that cycle,
and the protected raw pairing data retain their original orientation. -/
theorem native_actual_parent_partition_next_marked {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    {base : {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}}
    (c : (domainGraph (ParentDomain (outerFrame F A u hbase))).Walk base base)
    (hc : c.IsHamiltonianCycle)
    (pieces : List (Piece (domainGraph (ParentDomain (outerFrame F A u hbase)))))
    (cuts : Finset (Sym2 {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}))
    (hsupport : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail)
    (hedges : (pieces.flatMap fun p => p.walk.edges).Perm
      (c.edges.filter fun e => decide (e ∉ cuts)))
    (hcuts : ∀ e ∈ cuts, e ∈ c.edges) :
    let lift := parentNextMarkedMap F A u hbase hA
    let mapped := pieces.map (mapPiece lift)
    (c.map lift).IsHamiltonianCycle ∧
      (∀ p ∈ mapped, p.walk.IsPath) ∧
      (∀ v, (mapped.flatMap fun p => p.walk.support).count v = 1) ∧
      (mapped.flatMap fun p => p.walk.support).Perm (c.map lift).support.tail ∧
      (mapped.flatMap fun p => p.walk.edges).Perm
        ((c.map lift).edges.filter fun e => decide (e ∉ cuts.image (Sym2.map lift))) ∧
      (∀ e ∈ cuts.image (Sym2.map lift), e ∈ (c.map lift).edges) ∧
      ((mapped.flatMap fun p => p.walk.support).map Subtype.val) =
        (pieces.flatMap fun p => p.walk.support).map Subtype.val ∧
      ((mapped.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val)) =
        (pieces.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val) ∧
      (cuts.image (Sym2.map lift)).image (Sym2.map Subtype.val) =
        cuts.image (Sym2.map Subtype.val) := by
  dsimp only
  obtain ⟨_, hp, hs, he, hkept, _, _, hrawSupport, hrawEdges, hrawCuts, _⟩ :=
    native_actual_identity_partition_transport _ _ (parentNextMarkedMap F A u hbase hA)
      (fun _ => rfl) c hc.isCycle pieces cuts hsupport hedges hcuts
  have hnext : (c.map (parentNextMarkedMap F A u hbase hA)).IsHamiltonianCycle :=
    SimpleGraph.Walk.IsHamiltonianCycle.map (parent_next_marked_map_bijective F A u hbase hA) hc
  refine ⟨hnext, hp, ?_, hs, he, hkept, hrawSupport, hrawEdges, hrawCuts⟩
  intro v
  rw [hs.count_eq v]
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
    (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hnext).2 v

#print axioms native_actual_identity_partition_transport
#print axioms native_actual_parent_partition_next_marked

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateTransport
