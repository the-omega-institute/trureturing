/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/AlphaLabelledCodec
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/AlphaLabelledCodec
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Labelled deletion and insertion data for alpha avoidance. -/

import D5.S1.Words.Patterns.ArrowFixedPoint.AlphaDecomposition
import D5.S1.Words.Patterns.ArrowFixedPoint.LabelPartition

/-!
# Alpha labelled insertion

The high permutation is normalized on the labels above `M`.  Its transformed
one-line word supplies the high anchors.  The low labels occur once, globally
decreasing, in the slot before `M` and the slots following high anchors.  The
slot immediately after `M` is inserted as an empty piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm

noncomputable section

/-- Explicit alpha insertion data for a fixed largest label `M`. -/
structure AlphaLabelCode {n : ℕ} (M : Fin n) where
  sigma : Equiv.Perm (AboveIndex M)
  slots : Slots (Below M) (belowDescending M) (Fintype.card (Above M) + 1)
  singleton_positive : ∀ x : AboveIndex M, sigma x = x →
    0 < slots.lengths (Fin.succ ((theta sigma).symm x))

namespace AlphaLabelCode

variable {n : ℕ} {M : Fin n}

/-- `M`, followed by the actual standard high cycle word. -/
def anchors (code : AlphaLabelCode M) : List (Option (AboveIndex M)) :=
  none :: (List.ofFn (theta code.sigma)).map some

/-- Add the forbidden-after-`M` empty piece to the stored alpha slots. -/
def expandedPieces (code : AlphaLabelCode M) : List (List (Below M)) :=
  code.slots.pieces.headD [] :: [] :: code.slots.pieces.tail

theorem anchors_length (code : AlphaLabelCode M) :
    code.anchors.length = Fintype.card (Above M) + 1 := by
  simp [anchors]

theorem anchors_nodup (code : AlphaLabelCode M) : code.anchors.Nodup := by
  rw [anchors, List.nodup_cons]
  constructor
  · simp
  · exact (List.nodup_ofFn.mpr (theta code.sigma).injective).map
      (Option.some_injective _)

theorem mem_anchors (code : AlphaLabelCode M) (x : Option (AboveIndex M)) :
    x ∈ code.anchors := by
  rcases x with _ | x
  · simp [anchors]
  · simp only [anchors, List.mem_cons, Option.some_ne_none, false_or,
      List.mem_map, Option.some.injEq]
    exact ⟨x, by
      rw [List.mem_ofFn]
      exact ⟨(theta code.sigma).symm x,
        (theta code.sigma).apply_symm_apply x⟩, rfl⟩

theorem expandedPieces_length (code : AlphaLabelCode M) :
    code.expandedPieces.length = code.anchors.length + 1 := by
  have hne : code.slots.pieces ≠ [] := by
    intro h
    have := code.slots.length_eq
    simp [h] at this
  cases hpieces : code.slots.pieces with
  | nil => exact (hne hpieces).elim
  | cons piece pieces =>
      have hlen : pieces.length = Fintype.card (Above M) := by
        simpa [hpieces] using code.slots.length_eq
      simp [expandedPieces, anchors, hpieces, hlen]

theorem expandedPieces_flatten (code : AlphaLabelCode M) :
    code.expandedPieces.flatten = belowDescending M := by
  have hne : code.slots.pieces ≠ [] := by
    intro h
    have := code.slots.length_eq
    simp [h] at this
  cases hpieces : code.slots.pieces with
  | nil => exact (hne hpieces).elim
  | cons piece pieces =>
      simpa [expandedPieces, hpieces] using code.slots.flatten_eq

/-- The decoded word in low/middle/high coordinates. -/
def coloredWord (code : AlphaLabelCode M) :
    CompleteWord (Below M ⊕ Option (AboveIndex M)) :=
  completeWeave code.expandedPieces code.anchors code.expandedPieces_length
    (by rw [code.expandedPieces_flatten]; exact belowDescending_nodup M)
    (by rw [code.expandedPieces_flatten]; exact mem_belowDescending M)
    code.anchors_nodup code.mem_anchors

/-- The actual one-line word on `Fin n` decoded from the labelled alpha data. -/
def word (code : AlphaLabelCode M) : CompleteWord (Fin n) :=
  code.coloredWord.map (labelPartition M).symm

/-- Decode alpha insertion data to an actual one-line permutation. -/
def decode (code : AlphaLabelCode M) : Equiv.Perm (Fin n) :=
  code.word.toPermutation

/-- The actual one-line word determines every label and load in an alpha
insertion code with a fixed proposed largest label. -/
theorem decode_injective : Function.Injective (decode (M := M)) := by
  intro left right heq
  have recover (code : AlphaLabelCode M) :
      unweave ((List.ofFn code.decode).map (labelPartition M)) =
        (code.expandedPieces, code.anchors) := by
    rw [show List.ofFn code.decode = code.word.word from
      CompleteWord.ofFn_toPermutation code.word]
    change unweave ((code.coloredWord.word.map (labelPartition M).symm).map
      (labelPartition M)) = _
    simp only [List.map_map, Function.comp_def, Equiv.apply_symm_apply]
    simpa [coloredWord, completeWeave] using
      (unweave_weave code.expandedPieces code.anchors
        code.expandedPieces_length)
  have hread := recover left
  rw [heq, recover right] at hread
  have hpieces : left.expandedPieces = right.expandedPieces :=
    (congrArg Prod.fst hread).symm
  have hanchors : left.anchors = right.anchors :=
    (congrArg Prod.snd hread).symm
  have hhigh : List.ofFn (theta left.sigma) =
      List.ofFn (theta right.sigma) := by
    have htail := congrArg List.tail hanchors
    exact (List.map_injective_iff.mpr (Option.some_injective _))
      (by simpa [anchors] using htail)
  have hsigma : left.sigma = right.sigma :=
    theta.injective (Equiv.ext (fun x => congrFun (List.ofFn_injective hhigh) x))
  cases left with
  | mk sigmaLeft slotsLeft positiveLeft =>
      cases right with
      | mk sigmaRight slotsRight positiveRight =>
          dsimp at hsigma
          subst sigmaRight
          have hslots : slotsLeft.pieces = slotsRight.pieces := by
            have hleft : slotsLeft.pieces ≠ [] := by
              intro h
              have := slotsLeft.length_eq
              simp [h] at this
            have hright : slotsRight.pieces ≠ [] := by
              intro h
              have := slotsRight.length_eq
              simp [h] at this
            cases hl : slotsLeft.pieces with
            | nil => exact (hleft hl).elim
            | cons first rest =>
                cases hr : slotsRight.pieces with
                | nil => exact (hright hr).elim
                | cons first' rest' =>
                    simpa [expandedPieces, hl, hr] using hpieces
          have : slotsLeft = slotsRight := Slots.ext hslots
          subst slotsRight
          rfl

end AlphaLabelCode

end

end D5.S1.Words.Patterns.ArrowFixedPoint
