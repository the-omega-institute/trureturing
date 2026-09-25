/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/LabelPartition
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/LabelPartition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordered low, extremal, and high label coordinates for the arrow codecs. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.LabelledWords

/-!
# Label coordinates around an extremal fixed point

For `M : Fin n`, paper labels below `M.val + 1` form `Below M`; labels
strictly above it form `Above M`.  The latter are normalized increasingly to
`Fin (card (Above M))`.  The middle label is represented by `none`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv

noncomputable section

abbrev Below {n : ℕ} (M : Fin n) := {x : Fin n // x < M}
abbrev Above {n : ℕ} (M : Fin n) := {x : Fin n // M < x}
abbrev AboveIndex {n : ℕ} (M : Fin n) := Fin (Fintype.card (Above M))

/-- Increasing zero-based coordinates for labels below `M`. -/
def belowEquiv {n : ℕ} (M : Fin n) : Below M ≃ Fin M.val where
  toFun x := ⟨x.1.val, x.2⟩
  invFun i := ⟨⟨i.val, i.isLt.trans M.isLt⟩, i.isLt⟩
  left_inv x := by ext; rfl
  right_inv i := by ext; rfl

/-- The increasing normalization of labels strictly above `M`. -/
def aboveOrder {n : ℕ} (M : Fin n) : AboveIndex M ≃o Above M :=
  Fintype.orderIsoFinOfCardEq (Above M) rfl

/-- Raw trichotomy at `M`, retaining actual high labels. -/
def rawLabelPartition {n : ℕ} (M : Fin n) :
    Fin n ≃ Below M ⊕ Option (Above M) where
  toFun x :=
    if hlow : x < M then Sum.inl ⟨x, hlow⟩
    else if heq : x = M then Sum.inr none
    else Sum.inr (some ⟨x, lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm heq)⟩)
  invFun x := match x with
    | Sum.inl x => x.1
    | Sum.inr none => M
    | Sum.inr (some x) => x.1
  left_inv x := by
    dsimp
    by_cases hlow : x < M
    · simp [hlow]
    · by_cases heq : x = M
      · simp [hlow, heq]
      · simp [hlow, heq]
  right_inv x := by
    rcases x with x | x
    · simp [show x.1 < M from x.2]
    · rcases x with _ | x
      · simp
      · simp [x.2.asymm, x.2.ne']

/-- Trichotomy at `M` with the high labels normalized increasingly. -/
def labelPartition {n : ℕ} (M : Fin n) :
    Fin n ≃ Below M ⊕ Option (AboveIndex M) :=
  (rawLabelPartition M).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.optionCongr (aboveOrder M).symm.toEquiv))

/-- Low labels in forced decreasing order. -/
def belowDescending {n : ℕ} (M : Fin n) : List (Below M) :=
  (Finset.univ.sort (fun x y : Below M => y ≤ x))

theorem belowDescending_nodup {n : ℕ} (M : Fin n) :
    (belowDescending M).Nodup := by
  exact Finset.sort_nodup _ _

theorem mem_belowDescending {n : ℕ} (M : Fin n) (x : Below M) :
    x ∈ belowDescending M := by
  simp [belowDescending]

theorem belowDescending_length {n : ℕ} (M : Fin n) :
    (belowDescending M).length = M.val := by
  rw [belowDescending, Finset.length_sort, Finset.card_univ,
    Fintype.card_congr (belowEquiv M), Fintype.card_fin]

/-- Applying a label equivalence to a complete word preserves completeness. -/
def CompleteWord.map {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (word : CompleteWord α) : CompleteWord β where
  word := word.word.map e
  nodup := word.nodup.map e.injective
  complete y := List.mem_map.mpr ⟨e.symm y, word.complete _, e.apply_symm_apply y⟩

/-- A weave of complete left and right label lists is itself a complete word
on their disjoint sum. -/
def completeWeave {α β : Type*} [Fintype α] [Fintype β]
    (pieces : List (List α)) (anchors : List β)
    (hlength : pieces.length = anchors.length + 1)
    (hleftNodup : pieces.flatten.Nodup)
    (hleft : ∀ x : α, x ∈ pieces.flatten)
    (hrightNodup : anchors.Nodup)
    (hright : ∀ x : β, x ∈ anchors) : CompleteWord (α ⊕ β) where
  word := weave pieces anchors
  nodup := (weave_perm pieces anchors hlength).nodup_iff.mpr (by
    rw [List.nodup_append]
    refine ⟨hleftNodup.map Sum.inl_injective, hrightNodup.map Sum.inr_injective, ?_⟩
    simp)
  complete x := by
    rw [(weave_perm pieces anchors hlength).mem_iff]
    rcases x with x | x
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hleft x, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨x, hright x, rfl⟩)

end

end D5.S1.Words.Patterns.ArrowFixedPoint
