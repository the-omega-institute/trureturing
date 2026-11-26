module
public import Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Basic
import all Init.Data.String.Slice

/-! Logical strength of selecting a longest arbitrary string pattern match. -/

namespace OmegaChecks.InitInventory.StringPatterns

open String.Slice.Pattern.Model
private def sample : String.Slice := "a".toSlice
@[instance_reducible] private def acceptsEmptyOr (P : Prop) : PatternModel () := ⟨fun t => t = "" ∨ P⟩

/-- A longest forward match on a one-character string decides an arbitrary proposition. -/
public theorem excludedMiddleOfLongest (longest : type_of% @IsMatch.exists_isLongestMatch) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  have empty : IsMatch () sample.startPos := ⟨Or.inl rfl⟩
  obtain ⟨q, hq⟩ := longest empty
  cases hq.isMatch.matches_copy with
  | inr yes => exact Or.inl yes
  | inl eq =>
    right
    intro yes
    have atStart := q.splits.eq_startPos_iff.mpr eq
    exact hq.not_isMatch sample.endPos (atStart ▸ (by decide : sample.startPos < sample.endPos)) ⟨Or.inr yes⟩

/-- A longest reverse match on the same string decides an arbitrary proposition. -/
public theorem excludedMiddleOfRevLongest (longest : type_of% @IsRevMatch.exists_isLongestRevMatch) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  have empty : IsRevMatch () sample.endPos := ⟨Or.inl rfl⟩
  obtain ⟨q, hq⟩ := longest empty
  cases hq.isRevMatch.matches_copy with
  | inr yes => exact Or.inl yes
  | inl eq =>
    right
    intro yes
    have atEnd := q.splits.eq_endPos_iff.mpr eq
    exact hq.not_isRevMatch sample.startPos (atEnd ▸ (by decide : sample.startPos < sample.endPos)) ⟨Or.inr yes⟩

end OmegaChecks.InitInventory.StringPatterns
