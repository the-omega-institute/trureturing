/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBaseSlicing
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBaseSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct the Exceptional Actual Native Q Split. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQRouteSlicing
import D5.S3.Combinatorics.Graph.Walks.ActualBaseJointRouteSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBaseSlicing

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualBaseJointRouteSlicing

/-- At k2, the middle actual E2 path runs through three J2 pieces in
the literal order W1^0--W0^1, Z0^1--Z1^1, W1^1--W0^0. Restored marked
seams and the four retained a/b edges are earned from native coordinates
and the same supplied prior cycle. The fragments exhaust the supplied Λ. -/
theorem native_actual_q_base_three_fragments {m : ℕ} (hm : 3 ≤ m)
    (F₀ F₁ : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u])
    (hselected : F₀.selected.toFinset = F₁.selected.toFinset)
    (p q : Fin (m + 1)) (hp : p ∈ F₀.selected.toFinset) (hq : q ∈ F₀.selected.toFinset)
    (D : Configuration m → Prop)
    {base r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base)
    (hA : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) → s(x, y) ∈ w.edges)
    (hB : ∀ (x y : {v : Configuration m // D v}), y.val = x.val * b m →
      x.val (Fin.last m) ∉ F₀.selected.toFinset → s(x, y) ∈ w.edges)
    (p₁ p₂ p₃ : Piece (domainGraph D)) (rest : List (Piece (domainGraph D)))
    (hjn : ((p₁ :: p₂ :: p₃ :: rest).flatMap fun z => z.walk.support).Nodup)
    (hp₁finish : p₁.finish.val = leftPort (outerFrame F₁ A u hbase₁) 0)
    (hp₂start : p₂.start.val = rightPort (outerFrame F₁ A u hbase₁) 0)
    (hp₂finish : p₂.finish.val = rightPort (outerFrame F₁ A u hbase₁) 1)
    (hp₃start : p₃.start.val = leftPort (outerFrame F₁ A u hbase₁) 1)
    (hp₃finish : p₃.finish.val = leftPort (outerFrame F₀ A u hbase₀) 0)
    (K H : Finset (Sym2 {x : Configuration m // D x})) (hdisjoint : Disjoint K H)
    (hK : K.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₀ A u hbase₀))
    (hH : H.image (Sym2.map Subtype.val) = markedCuts (outerFrame F₁ A u hbase₁))
    (hjointInventory : ∀ e, e ∈ (p₁ :: p₂ :: p₃ :: rest).flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ K ∪ H)
    (hcuts : ∀ e ∈ K ∪ H, e ∈ w.edges)
    (p₀ p₄ : Piece (domainGraph D)) (old : (domainGraph D).Walk p₁.start p₃.finish)
    (hboundaryLink : Linked p₀ [⟨p₁.start, p₃.finish, old⟩, p₄])
    (hbn : ((p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
      fun z : Piece (domainGraph D) => z.walk.support).Nodup)
    (hboundaryInventory : ∀ e,
      e ∈ (p₀ :: ⟨p₁.start, p₃.finish, old⟩ :: p₄ :: []).flatMap
        (fun z : Piece (domainGraph D) => z.walk.edges) ↔ e ∈ w.edges ∧ e ∉ K)
    (Λ : (domainGraph D).Walk p₀.start p₄.finish)
    (hΛsupport : Λ.support = p₀.walk.support ++ old.support ++ p₄.walk.support)
    (hr₀ : r₀.val = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F₀ A u hbase₀) 0)
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F₀ A u hbase₀) 0) :
    ∃ q₀ : (domainGraph D).Walk p₀.start ℓ₀,
      ∃ q₁ : (domainGraph D).Walk r₀ ℓ₁,
      ∃ q₂ : (domainGraph D).Walk r₁ p₄.finish,
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = Λ.support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = Λ.edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  let edgeVal : Sym2 {x : Configuration m // D x} → Sym2 (Configuration m) :=
    Sym2.map Subtype.val
  have heinj : Function.Injective edgeVal := Sym2.map.injective Subtype.val_injective
  have hmemH (e : Sym2 {x : Configuration m // D x})
      (he : edgeVal e ∈ markedCuts (outerFrame F₁ A u hbase₁)) : e ∈ H := by
    rw [← hH] at he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact (heinj hfe) ▸ hf
  have hseam₁ : s(p₁.finish, p₂.start) ∈ H := by
    apply hmemH
    change s(p₁.finish.val, p₂.start.val) ∈ _
    rw [hp₁finish, hp₂start, Sym2.eq_swap]
    exact Finset.mem_image.mpr ⟨(0 : Fin 3), Finset.mem_univ _, rfl⟩
  have hseam₂ : s(p₂.finish, p₃.start) ∈ H := by
    apply hmemH
    change s(p₂.finish.val, p₃.start.val) ∈ _
    rw [hp₂finish, hp₃start]
    exact Finset.mem_image.mpr ⟨(1 : Fin 3), Finset.mem_univ _, rfl⟩
  have hcut₀ : (K ∪ H).image edgeVal =
      markedCuts (outerFrame F₀ A u hbase₀) ∪ markedCuts (outerFrame F₁ A u hbase₁) := by
    rw [Finset.image_union, hK, hH]
  have hcut₁ : (K ∪ H).image edgeVal =
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
      p q hp₁ hq₁ D w hA hB₁ (p₁ :: p₂ :: p₃ :: rest) (K ∪ H) hcut₁
      hjointInventory hp₁finish hr₀ hℓ₀
  obtain ⟨hba, hbb, hneq₁⟩ :=
    native_actual_q_zero_cut_retained hm F₀ (outerFrame F₁ A u hbase₁) A u hbase₀ rfl
      p q hp hq D w hA hB (p₁ :: p₂ :: p₃ :: rest) (K ∪ H) hcut₀
      hjointInventory hp₃finish hr₁ hℓ₁
  exact actual_base_joint_route_three_fragments w K H hdisjoint p₁ p₂ p₃ rest hjn
    hjointInventory hcuts hseam₁ hseam₂ p₀ p₄ old hboundaryLink hbn
    hboundaryInventory Λ hΛsupport hja hjb hneq₀ hba hbb hneq₁

#print axioms native_actual_q_base_three_fragments

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBaseSlicing
