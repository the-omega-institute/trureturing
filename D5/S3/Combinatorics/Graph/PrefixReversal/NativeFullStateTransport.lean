/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve Both Literal Native Boundary Orders. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
import D5.S3.Combinatorics.Graph.Walks.ActualTwoOrderStateTransport
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeFullStateTransport

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualTwoOrderStateTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels

/-- Identity on actual configurations carries all three partitions and
both native endpoint templates at once, including for a proper child
included in the ambient parent graph. No walk or piece is reselected. -/
theorem native_actual_identity_two_order_state_transport {m k : ℕ}
    (U V : Configuration m → Prop) (f : domainGraph U →g domainGraph V)
    (hval : ∀ x, (f x).val = x.val)
    (F₀ F₁ : SupplyFrame m k) (odd₀ odd₁ : Bool)
    {base : {x : Configuration m // U x}}
    (w : (domainGraph U).Walk base base)
    (K H : Finset (Sym2 {x : Configuration m // U x}))
    (joint primary opposite : List (Piece (domainGraph U)))
    (hs : ActualTwoOrderPartitions w K H joint primary opposite)
    (hp : NativeBoundaryPairs F₀ odd₀ Subtype.val primary)
    (ho : NativeBoundaryPairs F₁ odd₁ Subtype.val opposite) :
    let joint' := joint.map (mapPiece f)
    let primary' := primary.map (mapPiece f)
    let opposite' := opposite.map (mapPiece f)
    ActualTwoOrderPartitions (w.map f) (K.image (Sym2.map f)) (H.image (Sym2.map f))
      joint' primary' opposite' ∧
      NativeBoundaryPairs F₀ odd₀ Subtype.val primary' ∧
      NativeBoundaryPairs F₁ odd₁ Subtype.val opposite' ∧
      (K.image (Sym2.map f)).image (Sym2.map Subtype.val) = K.image (Sym2.map Subtype.val) ∧
      (H.image (Sym2.map f)).image (Sym2.map Subtype.val) = H.image (Sym2.map Subtype.val) := by
  dsimp only
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext ((hval x).symm.trans ((congrArg Subtype.val h).trans (hval y)))
  have hmapBoundary (F : SupplyFrame m k) (odd : Bool)
      (pieces : List (Piece (domainGraph U))) (hb : NativeBoundaryPairs F odd Subtype.val pieces) :
      NativeBoundaryPairs F odd Subtype.val (pieces.map (mapPiece f)) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, b, hqa, hqb, hpair⟩ := hb q hq
    exact ⟨a, b, (hval q.start).trans hqa, (hval q.finish).trans hqb, hpair⟩
  have hfun : Subtype.val ∘ f = (Subtype.val : {x : Configuration m // U x} → Configuration m) :=
    funext hval
  have hefun : Sym2.map Subtype.val ∘ Sym2.map f =
      (Sym2.map Subtype.val : Sym2 {x : Configuration m // U x} → Sym2 (Configuration m)) := by
    funext e
    rw [Function.comp_apply, Sym2.map_map, hfun]
  exact ⟨actual_two_order_state_map f hf w K H joint primary opposite hs,
    hmapBoundary F₀ odd₀ primary hp, hmapBoundary F₁ odd₁ opposite ho,
    by rw [Finset.image_image, hefun], by rw [Finset.image_image, hefun]⟩

#print axioms native_actual_identity_two_order_state_transport

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeFullStateTransport
