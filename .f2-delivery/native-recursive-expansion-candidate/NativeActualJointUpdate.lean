/- UNCOMPILED same-cycle native actual J propagation bridge.
   The complete closed-parent construction is mapped through the injective
   native-domain inclusion. Its actual cut set is identified by literal
   shifted native ports. The complete endpoint-pair update is earned from
   the actual old joint pieces and the three actual replacement walks.
   This is an induction-step interface, not an all-n existence theorem. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
import D5.S3.Combinatorics.Graph.Walks.ActualClosedParentJointUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs
open D5.S3.Combinatorics.Graph.Walks.ActualClosedParentJointUpdate

abbrev ParentVertex {m k : ℕ} (F : SupplyFrame m k) (A : List (Fin (m + 1)))
    (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) :=
  {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}

abbrev ParentGraph {m k : ℕ} (F : SupplyFrame m k) (A : List (Fin (m + 1)))
    (u : Fin (m + 1)) (hbase : F.base = A ++ [u]) :=
  domainGraph (ParentDomain (outerFrame F A u hbase))

private theorem mapped_complement_inventory {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (kept whole : List α) (cuts : Finset α)
    (hinv : ∀ e, e ∈ kept ↔ e ∈ whole ∧ e ∉ cuts) (e : β) :
    e ∈ kept.map f ↔ e ∈ whole.map f ∧ e ∉ cuts.image f := by
  constructor
  · intro he
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp he
    obtain ⟨hwhole, hnot⟩ := (hinv x).mp hx
    refine ⟨List.mem_map.mpr ⟨x, hwhole, hxe⟩, ?_⟩
    intro hcut
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hcut
    have hxy : x = y := hf (hxe.trans hye.symm)
    exact hnot (hxy.symm ▸ hy)
  · rintro ⟨he, hnot⟩
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp he
    apply List.mem_map.mpr
    refine ⟨x, (hinv x).mpr ⟨hx, ?_⟩, hxe⟩
    intro hcut
    exact hnot (Finset.mem_image.mpr ⟨x, hcut, hxe⟩)

/-- Every output piece belongs to the independently defined native parent
domain. The exact uncut native edges and endpoint-pair update concern the
same actual supplied parent cycle. Old marked edges and the two actual Q
cuts are identified with precisely the next two native marked orders. -/
theorem native_actual_closed_parent_joint_update {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F₀ F₁ : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase₀ : F₀.base = A ++ [u]) (hbase₁ : F₁.base = A ++ [u]) (ε : Bool)
    {base ℓ s t z a ℓ₀ r₀ ℓ₁ r₁ b : ParentVertex F₀ A u hbase₀}
    (c : (ParentGraph F₀ A u hbase₀).Walk base base) (hc : c.IsHamiltonianCycle)
    (d : (ParentGraph F₀ A u hbase₀).Walk ℓ z)
    (tail : (ParentGraph F₀ A u hbase₀).Walk t z)
    (hₐ : (ParentGraph F₀ A u hbase₀).Adj ℓ s)
    (h_b : (ParentGraph F₀ A u hbase₀).Adj s t)
    (hd : d = (tail.cons h_b).cons hₐ)
    (rest : List (Piece (ParentGraph F₀ A u hbase₀)))
    (P : (ParentGraph F₀ A u hbase₀).Walk s t)
    (deleted : List (Sym2 (ParentVertex F₀ A u hbase₀)))
    (hPs : P.support.Perm (d.support ++ rest.flatMap fun p => p.walk.support))
    (hPe : P.edges.Perm ((rest.flatMap fun p => p.walk.edges) ++
      tail.edges ++ [s(ℓ, s)] ++ deleted))
    (hdeleted : (deleted.map (Sym2.map Subtype.val)).toFinset = markedCuts F₀ ∪ markedCuts F₁)
    (Λ : (ParentGraph F₀ A u hbase₀).Walk a b)
    (q₀ : (ParentGraph F₀ A u hbase₀).Walk a ℓ₀)
    (q₁ : (ParentGraph F₀ A u hbase₀).Walk r₀ ℓ₁)
    (q₂ : (ParentGraph F₀ A u hbase₀).Walk r₁ b)
    (hQs : q₀.support ++ q₁.support ++ q₂.support = Λ.support)
    (hQe : q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges = Λ.edges)
    (others : List (Piece (ParentGraph F₀ A u hbase₀)))
    (hlink : Linked ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩]))
    (hbase : base = a) (hseam : (ParentGraph F₀ A u hbase₀).Adj t a)
    (hcs : c.support.tail =
      ((⟨a, b, Λ⟩ :: (others ++ [⟨s, t, P⟩])).flatMap
        fun p : Piece (ParentGraph F₀ A u hbase₀) => p.walk.support).reverse)
    (hce : c.edges = s(base, finish ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩])) ::
      (chainEdges ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩])).reverse)
    (hℓ : ℓ.val = leftPort F₀ 0)
    (hz : z.val = leftPort (if ε then F₁ else F₀) (k - 1))
    (hℓ₀ : ℓ₀.val = leftPort (nextFrame F₁ A u hbase₁) 0)
    (hr₀ : r₀.val = rightPort (nextFrame F₁ A u hbase₁) 0)
    (hℓ₁ : ℓ₁.val = leftPort (nextFrame F₀ A u hbase₀) 0)
    (hr₁ : r₁.val = rightPort (nextFrame F₀ A u hbase₀) 0) :
    let N₀ := nextFrame F₁ A u hbase₁
    let N₁ := nextFrame F₀ A u hbase₀
    let E := markedCuts N₀ ∪ markedCuts N₁
    ∃ pieces : List (Piece (ParentGraph F₀ A u hbase₀)),
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ x : Configuration m,
        (ParentDomain (outerFrame F₀ A u hbase₀) x →
          ((pieces.flatMap fun p => p.walk.support).map Subtype.val).count x = 1) ∧
        (¬ ParentDomain (outerFrame F₀ A u hbase₀) x →
          ((pieces.flatMap fun p => p.walk.support).map Subtype.val).count x = 0)) ∧
      (∀ e : Sym2 (Configuration m),
        e ∈ (pieces.flatMap fun p => p.walk.edges).map (Sym2.map Subtype.val) ↔
          e ∈ c.edges.map (Sym2.map Subtype.val) ∧ e ∉ E) ∧
      (∀ e ∈ E, e ∈ c.edges.map (Sym2.map Subtype.val)) ∧ pieces.length = E.card ∧
      (endpointPairs pieces).image (Sym2.map Subtype.val) =
        ((endpointPairs (⟨ℓ, z, d⟩ :: rest)).image (Sym2.map Subtype.val)).erase s(ℓ.val, z.val) ∪
          {s(leftPort (if ε then N₀ else N₁) k, leftPort N₀ 0),
            s(rightPort N₀ 0, leftPort N₁ 0), s(rightPort N₁ 0, leftPort N₁ 1)} := by
  classical
  dsimp only
  obtain ⟨chain, _, new₀, new₁, new₂, hpaths, hcount, _, _, hinv, hcuts,
      hcard, hpairs, _, _, _⟩ :=
    actual_closed_parent_joint_partition c hc d tail hₐ h_b hd rest P deleted hPs hPe
      Λ q₀ q₁ q₂ hQs hQe others hlink hbase hseam hcs hce
  let pieces : List (Piece (ParentGraph F₀ A u hbase₀)) :=
    [⟨z, ℓ₀, new₀⟩, ⟨r₀, ℓ₁, new₁⟩, ⟨r₁, ℓ, new₂⟩] ++ rest
  let cuts := (s(ℓ₀, r₀) :: s(ℓ₁, r₁) :: deleted).toFinset
  let edgeVal : Sym2 (ParentVertex F₀ A u hbase₀) → Sym2 (Configuration m) :=
    Sym2.map Subtype.val
  have heinj : Function.Injective edgeVal := Sym2.map.injective Subtype.val_injective
  have hzero₀ : edgeVal s(ℓ₀, r₀) = markedCut (nextFrame F₁ A u hbase₁) 0 := by
    change s(ℓ₀.val, r₀.val) = s(_, _)
    rw [hℓ₀, hr₀]
    exact Sym2.eq_swap
  have hzero₁ : edgeVal s(ℓ₁, r₁) = markedCut (nextFrame F₀ A u hbase₀) 0 := by
    change s(ℓ₁.val, r₁.val) = s(_, _)
    rw [hℓ₁, hr₁]
    exact Sym2.eq_swap
  have hcutimage : cuts.image edgeVal =
      markedCuts (nextFrame F₁ A u hbase₁) ∪ markedCuts (nextFrame F₀ A u hbase₀) := by
    rw [native_joint_marked_cuts_shift hm F₀ F₁ A u hbase₀ hbase₁]
    rw [← hdeleted, ← hzero₀, ← hzero₁]
    ext e
    simp [cuts, edgeVal, Finset.mem_image, List.mem_map, or_and_right, exists_or]
  have hrawcount (x : Configuration m) :
      (ParentDomain (outerFrame F₀ A u hbase₀) x →
        ((pieces.flatMap fun p => p.walk.support).map Subtype.val).count x = 1) ∧
      (¬ ParentDomain (outerFrame F₀ A u hbase₀) x →
        ((pieces.flatMap fun p => p.walk.support).map Subtype.val).count x = 0) := by
    constructor
    · intro hx
      let v : ParentVertex F₀ A u hbase₀ := ⟨x, hx⟩
      exact (List.count_map_of_injective _ Subtype.val Subtype.val_injective v).trans (hcount v)
    · intro hx
      apply List.count_eq_zero.mpr
      intro hmapped
      obtain ⟨v, _, hv⟩ := List.mem_map.mp hmapped
      exact hx (hv ▸ v.property)
  have hrawinv (e : Sym2 (Configuration m)) :
      e ∈ (pieces.flatMap fun p => p.walk.edges).map edgeVal ↔
        e ∈ c.edges.map edgeVal ∧
          e ∉ markedCuts (nextFrame F₁ A u hbase₁) ∪ markedCuts (nextFrame F₀ A u hbase₀) := by
    rw [← hcutimage]
    exact mapped_complement_inventory edgeVal heinj _ c.edges cuts
      (by intro f; simpa only [SimpleGraph.Walk.mem_edgeSet] using hinv f) e
  have hrawcuts (e : Sym2 (Configuration m))
      (he : e ∈ markedCuts (nextFrame F₁ A u hbase₁) ∪ markedCuts (nextFrame F₀ A u hbase₀)) :
      e ∈ c.edges.map edgeVal := by
    rw [← hcutimage] at he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact List.mem_map.mpr ⟨f, by simpa only [SimpleGraph.Walk.mem_edgeSet] using hcuts f hf, hfe⟩
  have hrawcard : pieces.length =
      (markedCuts (nextFrame F₁ A u hbase₁) ∪ markedCuts (nextFrame F₀ A u hbase₀)).card := by
    rw [← hcutimage, Finset.card_image_of_injective _ heinj]
    exact hcard
  have hℓnext : ℓ.val = leftPort (nextFrame F₀ A u hbase₀) 1 :=
    hℓ.trans (native_marked_index_shift hm F₀ A u hbase₀ 0).2.symm
  have hznext : z.val = leftPort
      (if ε then nextFrame F₁ A u hbase₁ else nextFrame F₀ A u hbase₀) k := by
    have hkindex : k - 1 + 1 = k := by omega
    cases ε with
    | false =>
      have hs := (native_marked_index_shift hm F₀ A u hbase₀ (k - 1)).2
      rw [hkindex] at hs
      exact hz.trans hs.symm
    | true =>
      have hs := (native_marked_index_shift hm F₁ A u hbase₁ (k - 1)).2
      rw [hkindex] at hs
      exact hz.trans hs.symm
  refine ⟨pieces, hpaths, hrawcount, hrawinv, hrawcuts, hrawcard, ?_⟩
  have h := congrArg (Finset.image edgeVal) hpairs
  rw [Finset.image_union, Finset.image_erase heinj] at h
  simpa only [edgeVal, Finset.image_insert, Finset.image_singleton, Sym2.map_mk,
    hℓ₀, hr₀, hℓ₁, hr₁, hℓnext, hznext] using h

#print axioms native_actual_closed_parent_joint_update

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate
