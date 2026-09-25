/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/LabelledWords
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/LabelledWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Complete finite words and reversible labelled slot insertion. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.CycleWord
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.List.SplitLengths

/-!
# Complete labelled words

This file contains the finite word operations shared by the two source
codecs.  A complete word lists every label once.  `weave` inserts an ordered
list of anchors between consecutive pieces, while `unweave` recovers those
pieces without losing empty slots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv

noncomputable section

/-- A finite word containing each label exactly once. -/
structure CompleteWord (α : Type*) [Fintype α] where
  word : List α
  nodup : word.Nodup
  complete : ∀ x : α, x ∈ word

namespace CompleteWord

@[ext]
theorem ext {α : Type*} [Fintype α] {u v : CompleteWord α}
    (h : u.word = v.word) : u = v := by
  cases u
  cases v
  cases h
  rfl

/-- A complete word on `Fin n` is its positional one-line permutation. -/
def toPermutation {n : ℕ} (w : CompleteWord (Fin n)) : Equiv.Perm (Fin n) :=
  let e := w.nodup.getEquivOfForallMemList w.word w.complete
  let hlength : w.word.length = n := by
    simpa [e] using Fintype.card_congr e
  (finCongr hlength.symm).trans e

theorem ofFn_toPermutation {n : ℕ} (w : CompleteWord (Fin n)) :
    List.ofFn w.toPermutation = w.word := by
  let e := w.nodup.getEquivOfForallMemList w.word w.complete
  let hlength : w.word.length = n := by
    simpa [e] using Fintype.card_congr e
  change List.ofFn ((finCongr hlength.symm).trans e) = w.word
  rw [List.ofFn_congr hlength.symm]
  exact List.ofFn_get w.word

/-- The complete word read from a one-line permutation. -/
def ofPermutation {n : ℕ} (p : Equiv.Perm (Fin n)) : CompleteWord (Fin n) where
  word := List.ofFn p
  nodup := List.nodup_ofFn.mpr p.injective
  complete := fun x => by
    rw [List.mem_ofFn]
    exact ⟨p.symm x, p.apply_symm_apply x⟩

theorem toPermutation_ofPermutation {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (ofPermutation p).toPermutation = p := by
  apply Equiv.ext
  exact congrFun (List.ofFn_injective <| by
    simpa [ofPermutation] using ofFn_toPermutation (ofPermutation p))

/-- Complete words on `Fin n` and one-line permutations carry exactly the
same labelled data. -/
def equivPermutation (n : ℕ) : CompleteWord (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun := toPermutation
  invFun := ofPermutation
  left_inv := fun w => ext (ofFn_toPermutation w)
  right_inv := toPermutation_ofPermutation

end CompleteWord

/-- Insert the anchors between consecutive pieces.  With `r + 1` pieces and
`r` anchors, the first and last pieces are the two boundary slots. -/
def weave {α β : Type*} : List (List α) → List β → List (α ⊕ β)
  | [], _ => []
  | piece :: _, [] => piece.map Sum.inl
  | piece :: pieces, anchor :: anchors =>
      piece.map Sum.inl ++ Sum.inr anchor :: weave pieces anchors

/-- Recover every (possibly empty) left-labelled piece and the right-labelled
anchors from a woven word. -/
def unweave {α β : Type*} : List (α ⊕ β) → List (List α) × List β
  | [] => ([[]], [])
  | Sum.inl x :: word =>
      match unweave word with
      | ([], anchors) => ([[x]], anchors)
      | (piece :: pieces, anchors) => ((x :: piece) :: pieces, anchors)
  | Sum.inr x :: word =>
      let result := unweave word
      ([] :: result.1, x :: result.2)

private theorem unweave_pieces_ne_nil {α β : Type*} (word : List (α ⊕ β)) :
    (unweave word).1 ≠ [] := by
  induction word with
  | nil => simp [unweave]
  | cons x word ih =>
      cases x with
      | inl x =>
          simp only [unweave]
          cases h : unweave word with
          | mk pieces anchors =>
              cases pieces <;> simp
      | inr x => simp [unweave]

private theorem unweave_inl {α β : Type*} (x : α) (word : List (α ⊕ β)) :
    unweave (Sum.inl x :: word) =
      ((x :: (unweave word).1.headD []) ::
        (unweave word).1.tail, (unweave word).2) := by
  simp only [unweave]
  cases h : unweave word with
  | mk pieces anchors =>
      have hp : pieces ≠ [] := by
        simpa [h] using unweave_pieces_ne_nil word
      cases pieces with
      | nil => exact (hp rfl).elim
      | cons piece pieces => simp [h]

private theorem unweave_inr {α β : Type*} (x : β) (word : List (α ⊕ β)) :
    unweave (Sum.inr x :: word) =
      ([] :: (unweave word).1, x :: (unweave word).2) := by
  rfl

private theorem unweave_map_inl_append {α β : Type*}
    (front : List α) (word : List (α ⊕ β)) :
    unweave (front.map Sum.inl ++ word) =
      ((front ++ (unweave word).1.headD []) ::
        (unweave word).1.tail, (unweave word).2) := by
  induction front with
  | nil =>
      simp only [List.map_nil, List.nil_append, List.nil_append]
      cases h : unweave word with
      | mk pieces anchors =>
          have hp : pieces ≠ [] := by
            simpa [h] using unweave_pieces_ne_nil word
          cases pieces with
          | nil => exact (hp rfl).elim
          | cons piece pieces => simp [h]
  | cons x front ih =>
      simp only [List.map_cons, List.cons_append, unweave_inl]
      rw [ih]
      simp

theorem unweave_weave {α β : Type*} (pieces : List (List α)) (anchors : List β)
    (hlength : pieces.length = anchors.length + 1) :
    unweave (weave pieces anchors) = (pieces, anchors) := by
  induction anchors generalizing pieces with
  | nil =>
      cases pieces with
      | nil => simp at hlength
      | cons piece pieces =>
          have : pieces = [] := by simpa using hlength
          subst pieces
          simp only [weave]
          simpa [unweave] using (unweave_map_inl_append (β := β) piece [])
  | cons anchor anchors ih =>
      cases pieces with
      | nil => simp at hlength
      | cons piece pieces =>
          have htail : pieces.length = anchors.length + 1 := by simpa using hlength
          simp only [weave, unweave_map_inl_append, unweave_inr]
          rw [ih pieces htail]
          simp

theorem unweave_length {α β : Type*} (word : List (α ⊕ β)) :
    (unweave word).1.length = (unweave word).2.length + 1 := by
  induction word with
  | nil => simp [unweave]
  | cons x word ih =>
      cases x with
      | inl x =>
          rw [unweave_inl]
          cases h : unweave word with
          | mk pieces anchors =>
              have hp : pieces ≠ [] := by
                simpa [h] using unweave_pieces_ne_nil word
              cases pieces with
              | nil => exact (hp rfl).elim
              | cons piece pieces => simpa [h] using ih
      | inr x => simp [unweave_inr, ih]

theorem weave_unweave {α β : Type*} (word : List (α ⊕ β)) :
    weave (unweave word).1 (unweave word).2 = word := by
  induction word with
  | nil => rfl
  | cons x word ih =>
      cases x with
      | inl x =>
          rw [unweave_inl]
          cases h : unweave word with
          | mk pieces anchors =>
              have hp : pieces ≠ [] := by
                simpa [h] using unweave_pieces_ne_nil word
              have hlen : pieces.length = anchors.length + 1 := by
                simpa [h] using unweave_length word
              have hi : weave pieces anchors = word := by simpa [h] using ih
              cases pieces with
              | nil => exact (hp rfl).elim
              | cons piece pieces =>
                  cases anchors with
                  | nil =>
                      have : pieces = [] := by simpa using hlen
                      subst pieces
                      simpa [weave, h] using congrArg (List.cons (Sum.inl x)) hi
                  | cons anchor anchors =>
                      simpa [weave, h] using congrArg (List.cons (Sum.inl x)) hi
      | inr x =>
          rw [unweave_inr]
          simpa [weave] using congrArg (List.cons (Sum.inr x)) ih

theorem unweave_flatten {α β : Type*} (word : List (α ⊕ β)) :
    (unweave word).1.flatten =
      word.filterMap (fun x => match x with | Sum.inl a => some a | Sum.inr _ => none) := by
  induction word with
  | nil => simp [unweave]
  | cons x word ih =>
      cases x with
      | inl x =>
          simp only [unweave]
          cases h : unweave word with
          | mk pieces anchors =>
              have hp : pieces ≠ [] := by
                simpa [h] using unweave_pieces_ne_nil word
              cases pieces with
              | nil => exact (hp rfl).elim
              | cons piece pieces => simpa [h] using congrArg (List.cons x) ih
      | inr x => simp [unweave, ih]

theorem unweave_anchors {α β : Type*} (word : List (α ⊕ β)) :
    (unweave word).2 =
      word.filterMap (fun x => match x with | Sum.inl _ => none | Sum.inr b => some b) := by
  induction word with
  | nil => simp [unweave]
  | cons x word ih => cases x <;> simp [unweave_inl, unweave_inr, ih]

theorem weave_perm {α β : Type*} (pieces : List (List α)) (anchors : List β)
    (hlength : pieces.length = anchors.length + 1) :
    List.Perm (weave pieces anchors)
      (pieces.flatten.map Sum.inl ++ anchors.map Sum.inr) := by
  induction anchors generalizing pieces with
  | nil =>
      cases pieces with
      | nil => simp at hlength
      | cons piece pieces =>
          have : pieces = [] := by simpa using hlength
          subst pieces
          simp [weave]
  | cons anchor anchors ih =>
      cases pieces with
      | nil => simp at hlength
      | cons piece pieces =>
          have htail : pieces.length = anchors.length + 1 := by simpa using hlength
          simp only [weave, List.flatten_cons, List.map_append, List.map_cons]
          refine ((List.Perm.refl _).append
            (List.Perm.cons _ (ih pieces htail))).trans ?_
          simpa [List.append_assoc] using
            (List.Perm.append_left (piece.map Sum.inl)
              (List.perm_middle (a := Sum.inr anchor)
                (l₁ := pieces.flatten.map Sum.inl)
                (l₂ := anchors.map Sum.inr)).symm)

/-- Consecutive pieces whose flattening is a prescribed list. -/
structure Slots (α : Type*) (labels : List α) (slotCount : ℕ) where
  pieces : List (List α)
  length_eq : pieces.length = slotCount
  flatten_eq : pieces.flatten = labels

namespace Slots

@[ext]
theorem ext {α : Type*} {labels : List α} {slotCount : ℕ}
    {u v : Slots α labels slotCount} (h : u.pieces = v.pieces) : u = v := by
  cases u
  cases v
  cases h
  rfl

/-- Slot lengths determine the consecutive pieces uniquely. -/
def lengths {α : Type*} {labels : List α} {slotCount : ℕ}
    (s : Slots α labels slotCount) : Fin slotCount → ℕ := fun i =>
  s.pieces.get (Fin.cast s.length_eq.symm i)
    |>.length

theorem ofFn_lengths {α : Type*} {labels : List α} {slotCount : ℕ}
    (s : Slots α labels slotCount) :
    List.ofFn s.lengths = s.pieces.map List.length := by
  apply List.ext_getElem
  · simpa using s.length_eq.symm
  · intro i hleft hright
    simp [lengths]

theorem sum_lengths {α : Type*} {labels : List α} {slotCount : ℕ}
    (s : Slots α labels slotCount) : ∑ i, s.lengths i = labels.length := by
  rw [← List.sum_ofFn, s.ofFn_lengths, ← List.length_flatten, s.flatten_eq]

private theorem splitLengths_map_length_flatten {α : Type*}
    (pieces : List (List α)) :
    (pieces.map List.length).splitLengths pieces.flatten = pieces := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      simp only [List.map_cons, List.flatten_cons, List.splitLengths_cons]
      rw [List.take_left, List.drop_left, ih]

/-- A slot decomposition is exactly a weak composition of the number of
labels into the prescribed number of ordered slots. -/
def equivNatSum {α : Type*} {labels : List α} (slotCount : ℕ) :
    Slots α labels slotCount ≃
      {loads : Fin slotCount → ℕ // ∑ i, loads i = labels.length} where
  toFun s := ⟨s.lengths, s.sum_lengths⟩
  invFun loads :=
    { pieces := (List.ofFn loads.1).splitLengths labels
      length_eq := by simp
      flatten_eq := List.flatten_splitLengths _ _ (by
        rw [List.sum_ofFn, loads.2]) }
  left_inv s := by
    apply ext
    change (List.ofFn s.lengths).splitLengths labels = s.pieces
    rw [s.ofFn_lengths]
    calc
      (s.pieces.map List.length).splitLengths labels =
          (s.pieces.map List.length).splitLengths s.pieces.flatten :=
        congrArg _ s.flatten_eq.symm
      _ = s.pieces := splitLengths_map_length_flatten s.pieces
  right_inv loads := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [ofFn_lengths]
    exact List.map_splitLengths_length labels (List.ofFn loads.1) (by
      rw [List.sum_ofFn, loads.2])

/-- The stars-and-bars model of ordered slots. -/
def equivSym {α : Type*} {labels : List α} (slotCount : ℕ) :
    Slots α labels slotCount ≃ Sym (Fin slotCount) labels.length :=
  (equivNatSum slotCount).trans (Sym.equivNatSumOfFintype _ _).symm

noncomputable instance fintype {α : Type*} {labels : List α} {slotCount : ℕ} :
    Fintype (Slots α labels slotCount) :=
  Fintype.ofEquiv (Sym (Fin slotCount) labels.length) (equivSym slotCount).symm

theorem card {α : Type*} {labels : List α} (slotCount : ℕ) :
    Fintype.card (Slots α labels slotCount) =
      (slotCount + labels.length - 1).choose labels.length := by
  rw [Fintype.card_congr (equivSym slotCount), Sym.card_sym_eq_choose]
  simp

end Slots

end

end D5.S1.Words.Patterns.ArrowFixedPoint
