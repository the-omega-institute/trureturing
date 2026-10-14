/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve Both Literal Native Boundary Orders. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateTransport
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

/-- The completed actual parent state becomes the next marked induction
state on exactly this mapped Hamilton cycle. Its three partitions, two
native endpoint templates, both cut groups and both retention invariants
are transported together across the earned domain identification. -/
theorem native_actual_full_parent_state_next_marked {m k : ℕ}
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (F₀ F₁ : SupplyFrame m (k + 1)) (odd₀ odd₁ : Bool) (p q : Fin (m + 1))
    {base : {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}}
    (c : (domainGraph (ParentDomain (outerFrame F A u hbase))).Walk base base)
    (hc : c.IsHamiltonianCycle)
    (K H : Finset (Sym2 {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}))
    (joint primary opposite : List (Piece (domainGraph (ParentDomain (outerFrame F A u hbase)))))
    (hs : ActualTwoOrderPartitions c K H joint primary opposite)
    (hp : NativeBoundaryPairs F₀ odd₀ Subtype.val primary)
    (ho : NativeBoundaryPairs F₁ odd₁ Subtype.val opposite)
    (hkeepA : ∀ (x y : {v : Configuration m // ParentDomain (outerFrame F A u hbase) v}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ c.edges)
    (hkeepB : ∀ (x y : {v : Configuration m // ParentDomain (outerFrame F A u hbase) v}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ insert u F.selected.toFinset →
        s(x, y) ∈ c.edges) :
    let N := nextFrame F A u hbase
    let hN : 3 ≤ N.base.length := by simpa only [N, nextFrame] using hA
    let lift := parentNextMarkedMap F A u hbase hA
    let next := c.map lift
    next.IsHamiltonianCycle ∧
      ActualTwoOrderPartitions next (K.image (Sym2.map lift)) (H.image (Sym2.map lift))
        (joint.map (mapPiece lift)) (primary.map (mapPiece lift)) (opposite.map (mapPiece lift)) ∧
      NativeBoundaryPairs F₀ odd₀ Subtype.val (primary.map (mapPiece lift)) ∧
      NativeBoundaryPairs F₁ odd₁ Subtype.val (opposite.map (mapPiece lift)) ∧
      next.support.map Subtype.val = c.support.map Subtype.val ∧
      next.edges.map (Sym2.map Subtype.val) = c.edges.map (Sym2.map Subtype.val) ∧
      (K.image (Sym2.map lift)).image (Sym2.map Subtype.val) = K.image (Sym2.map Subtype.val) ∧
      (H.image (Sym2.map lift)).image (Sym2.map Subtype.val) = H.image (Sym2.map Subtype.val) ∧
      (∀ (x y : {v : Configuration m // SpecialDomain N hN v}),
        y.val = x.val * a m →
        s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ next.edges) ∧
      (∀ (x y : {v : Configuration m // SpecialDomain N hN v}),
        y.val = x.val * b m → x.val (Fin.last m) ∉ N.selected.toFinset →
          s(x, y) ∈ next.edges) ∧
      (∀ hk : 2 ≤ k,
        protectedP N (by omega) = protectedP F hk ∧
          protectedQ N (by omega) = protectedQ F hk) := by
  dsimp only
  obtain ⟨hstate, hprimary, hopposite, hK, hH⟩ :=
    native_actual_identity_two_order_state_transport _ _ (parentNextMarkedMap F A u hbase hA)
      (fun _ => rfl) F₀ F₁ odd₀ odd₁ c K H joint primary opposite hs hp ho
  obtain ⟨hnext, hsupport, hedges, hnextA, hnextB⟩ :=
    native_same_parent_cycle_next_marked F A u hbase hA p q c hc hkeepA hkeepB
  exact ⟨hnext, hstate, hprimary, hopposite, hsupport, hedges, hK, hH, hnextA, hnextB,
    fun hk => native_protected_labels_prepend F (nextFrame F A u hbase) hk u rfl⟩

#print axioms native_actual_identity_two_order_state_transport
#print axioms native_actual_full_parent_state_next_marked

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeFullStateTransport
