/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQRouteSlicing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualQRouteSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Slice the Same Actual Native Q Route. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeBoundaryRoutePositions
import D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQRouteSlicing

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing

/-- Consume the literal prior native joint and single-order inventories.
The later boundary endpoint is supplied by the native E/O route position;
the four retained edges and their local occurrence are all conclusions of
the same-cycle invariants. The final fragments belong to the supplied Λ. -/
theorem native_actual_q_route_three_fragments {m k : ℕ} (hm : 3 ≤ m)
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (p q : Fin (m + 1)) (hp : p ∈ F₀.selected.toFinset) (hq : q ∈ F₀.selected.toFinset)
    (D : Configuration m → Prop)
    {base w₀ w₁ r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base)
    (hA : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hB : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * b m →
      x.val (Fin.last m) ∉ F₀.selected.toFinset → s(x, y) ∈ w.edges)
    (joint : List (Piece (domainGraph D)))
    (hjn : (joint.flatMap fun z => z.walk.support).Nodup)
    (jp : Piece (domainGraph D)) (hjp : jp ∈ joint) (hjpath : jp.walk.IsPath)
    (first : Piece (domainGraph D)) (later : List (Piece (domainGraph D)))
    (hlink : Linked first later)
    (Λ : (domainGraph D).Walk first.start (finish first later))
    (hΛsupport : Λ.support = (first :: later).flatMap fun z => z.walk.support)
    (hbn : ((first :: later).flatMap fun z => z.walk.support).Nodup)
    (hbpath : ∀ z ∈ first :: later, z.walk.IsPath)
    (hroot : jp.start = first.start)
    (K H : Finset (Sym2 {x : Configuration m // D x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₀ A u hbase₀))
    (hH : H.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₁ A u hbase₁))
    (hjointInventory : ∀ e, e ∈ joint.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hboundaryInventory : ∀ e, e ∈ (first :: later).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K)
    {i : ℕ} (hipos : 0 < i) (hi : i < (first :: later).length)
    (hjfinish : jp.finish = w₁)
    (hbfinish : ((first :: later)[i]'hi).finish = w₀)
    (hw₀ : w₀.val = leftPort (outerFrame F₀ A u hbase₀) 0)
    (hw₁ : w₁.val = leftPort (outerFrame F₁ A u hbase₁) 0)
    (hr₀ : r₀.val = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F₀ A u hbase₀) 0)
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F₀ A u hbase₀) 0) :
    ∃ q₀ : (domainGraph D).Walk first.start ℓ₀,
      ∃ q₁ : (domainGraph D).Walk r₀ ℓ₁,
      ∃ q₂ : (domainGraph D).Walk r₁ (finish first later),
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  have hcut₀ : (K ∪ H).image (Sym2.map Subtype.val) =
      markedCuts (outerFrame F₀ A u hbase₀) ∪ markedCuts (outerFrame F₁ A u hbase₁) := by
    rw [Finset.image_union, hK, hH]
  have hcut₁ : (K ∪ H).image (Sym2.map Subtype.val) =
      markedCuts (outerFrame F₁ A u hbase₁) ∪ markedCuts (outerFrame F₀ A u hbase₀) := by
    rw [hcut₀, Finset.union_comm]
  have hp₁ : p ∈ F₁.selected.toFinset := hselected ▸ hp
  have hq₁ : q ∈ F₁.selected.toFinset := hselected ▸ hq
  have hB₁ : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * b m →
      x.val (Fin.last m) ∉ F₁.selected.toFinset → s(x, y) ∈ w.edges := by
    intro x y hxy ht
    exact hB x y hxy (hselected.symm ▸ ht)
  obtain ⟨hja, hjb, hneq₀⟩ :=
    native_actual_q_zero_cut_retained hm F₁ (outerFrame F₀ A u hbase₀) A u hbase₁ rfl
      p q hp₁ hq₁ D w hA hB₁ joint (K ∪ H) hcut₁ hjointInventory hw₁ hr₀ hℓ₀
  obtain ⟨hba, hbb, hneq₁⟩ :=
    native_actual_q_zero_cut_retained hm F₀ (outerFrame F₁ A u hbase₁) A u hbase₀ rfl
      p q hp hq D w hA hB joint (K ∪ H) hcut₀ hjointInventory hw₀ hr₁ hℓ₁
  exact actual_joint_and_route_three_fragments joint hjn jp hjp hjpath
    first later hlink Λ hΛsupport hbn hbpath hroot w K H
    hjointInventory hboundaryInventory hipos hi hjfinish hbfinish
    hja hjb hneq₀ hba hbb hneq₁

#print axioms native_actual_q_route_three_fragments

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQRouteSlicing
