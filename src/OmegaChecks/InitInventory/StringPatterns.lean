module
public import Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Basic
import all Init.Data.String.Slice

/-! Logical strength of selecting a longest arbitrary string pattern match. -/

namespace OmegaChecks.InitInventory.StringPatterns

open String.Slice.Pattern.Model
private def sample : String.Slice := "a".toSlice
@[instance_reducible] private def acceptsEmptyOr (P : Prop) : PatternModel () := ⟨fun t => t = "" ∨ P⟩

private theorem decideFromForward (P : Prop)
    (h : @Exists sample.Pos (fun q => @IsLongestMatch _ () (acceptsEmptyOr P) sample q)) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  obtain ⟨q, hq⟩ := h
  cases hq.isMatch.matches_copy with
  | inr yes => exact Or.inl yes
  | inl eq =>
    right
    intro yes
    have atStart := q.splits.eq_startPos_iff.mpr eq
    exact hq.not_isMatch sample.endPos (atStart ▸ (by decide : sample.startPos < sample.endPos)) ⟨Or.inr yes⟩

private theorem decideFromBackward (P : Prop)
    (h : @Exists sample.Pos (fun q => @IsLongestRevMatch _ () (acceptsEmptyOr P) sample q)) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  obtain ⟨q, hq⟩ := h
  cases hq.isRevMatch.matches_copy with
  | inr yes => exact Or.inl yes
  | inl eq =>
    right
    intro yes
    have atEnd := q.splits.eq_endPos_iff.mpr eq
    exact hq.not_isRevMatch sample.startPos (atEnd ▸ (by decide : sample.startPos < sample.endPos)) ⟨Or.inr yes⟩

/-- A longest forward match on a one-character string decides an arbitrary proposition. -/
public theorem excludedMiddleOfLongest (longest : type_of% @IsMatch.exists_isLongestMatch) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  exact decideFromForward P (longest (show IsMatch () sample.startPos from ⟨Or.inl rfl⟩))

/-- A longest reverse match on the same string decides an arbitrary proposition. -/
public theorem excludedMiddleOfRevLongest (longest : type_of% @IsRevMatch.exists_isLongestRevMatch) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  exact decideFromBackward P (longest (show IsRevMatch () sample.endPos from ⟨Or.inl rfl⟩))

public theorem excludedMiddleOfMatchesAt (existsMatch : type_of% @matchesAt_iff_exists_isMatch)
    (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  have matchAtStart : MatchesAt () sample.startPos := existsMatch.mpr
    ⟨sample.startPos, Nat.le_refl _, ⟨Or.inl (by decide)⟩⟩
  obtain ⟨pos, longest⟩ := matchAtStart
  exact decideFromForward P ⟨pos, isLongestMatchAt_startPos_iff.mp longest⟩

public theorem excludedMiddleOfRevMatchesAt (existsMatch : type_of% @revMatchesAt_iff_exists_isRevMatch)
    (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := acceptsEmptyOr P
  have matchAtEnd : RevMatchesAt () sample.endPos := existsMatch.mpr
    ⟨sample.endPos, Nat.le_refl _, ⟨Or.inl (by decide)⟩⟩
  obtain ⟨pos, longest⟩ := matchAtEnd
  exact decideFromBackward P ⟨pos, isLongestRevMatchAt_endPos_iff.mp longest⟩

@[instance_reducible] private def accepts (P : Prop) : PatternModel () := ⟨fun _ => P⟩

private theorem matchesWhole (P : Prop) (h : P) :
    @IsLongestMatchAt _ () (accepts P) sample sample.startPos sample.endPos := by
  letI : PatternModel () := accepts P
  apply isLongestMatchAt_startPos_iff.mpr
  exact ⟨⟨h⟩, fun q beyond _ => Nat.not_lt_of_ge q.isValidForSlice.le_utf8ByteSize beyond⟩

private theorem revMatchesWhole (P : Prop) (h : P) :
    @IsLongestRevMatchAt _ () (accepts P) sample sample.startPos sample.endPos := by
  letI : PatternModel () := accepts P
  apply isLongestRevMatchAt_endPos_iff.mpr
  exact ⟨⟨h⟩, fun _ before _ => Nat.not_lt_zero _ before⟩

/-- The successful-result specification of any forward matcher decides every proposition. -/
public theorem excludedMiddleOfForwardResult (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat a = some b ↔ IsLongestMatchAt pat a b) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := accepts P
  cases result : find () sample.startPos with
  | some q => exact Or.inl ((correct.mp result).isLongestMatch_sliceFrom.isMatch.matches_copy)
  | none =>
    right
    intro yes
    have clash := result.symm.trans (correct.mpr (matchesWhole P yes))
    cases clash

/-- The successful-result specification of any reverse matcher decides every proposition. -/
public theorem excludedMiddleOfBackwardResult (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat b = some a ↔ IsLongestRevMatchAt pat a b) (P : Prop) : P ∨ ¬ P := by
  letI : PatternModel () := accepts P
  cases result : find () sample.endPos with
  | some q => exact Or.inl ((correct.mp result).isLongestRevMatch_sliceTo.isRevMatch.matches_copy)
  | none =>
    right
    intro yes
    have clash := result.symm.trans (correct.mpr (revMatchesWhole P yes))
    cases clash

public theorem excludedMiddleOfMatchAtSome (spec : type_of% @matchAt?_eq_some_iff) :
    ∀ P : Prop, P ∨ ¬ P := excludedMiddleOfForwardResult (@matchAt?) spec

public theorem excludedMiddleOfRevMatchAtSome (spec : type_of% @revMatchAt?_eq_some_iff) :
    ∀ P : Prop, P ∨ ¬ P := excludedMiddleOfBackwardResult (@revMatchAt?) spec

/-- Weak excluded middle decides the negation of each proposition. -/
public def WeakExcludedMiddle : Prop := ∀ P : Prop, ¬ P ∨ ¬ ¬ P

public theorem weakExcludedMiddleOfForwardFailure (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a : s.Pos},
      find pat a = none ↔ ¬ MatchesAt pat a) : WeakExcludedMiddle := by
  intro P
  letI : PatternModel () := accepts P
  cases result : find () sample.startPos with
  | none => exact Or.inl fun yes => correct.mp result ⟨⟨_, matchesWhole P yes⟩⟩
  | some q =>
    right
    intro no
    have absent : ¬ MatchesAt () sample.startPos := by
      rintro ⟨⟨_, hit⟩⟩
      exact no hit.isLongestMatch_sliceFrom.isMatch.matches_copy
    cases result.symm.trans (correct.mpr absent)

public theorem weakExcludedMiddleOfBackwardFailure (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {b : s.Pos},
      find pat b = none ↔ ¬ RevMatchesAt pat b) : WeakExcludedMiddle := by
  intro P
  letI : PatternModel () := accepts P
  cases result : find () sample.endPos with
  | none => exact Or.inl fun yes => correct.mp result ⟨⟨_, revMatchesWhole P yes⟩⟩
  | some q =>
    right
    intro no
    have absent : ¬ RevMatchesAt () sample.endPos := by
      rintro ⟨⟨_, hit⟩⟩
      exact no hit.isLongestRevMatch_sliceTo.isRevMatch.matches_copy
    cases result.symm.trans (correct.mpr absent)

public theorem weakExcludedMiddleOfMatchAtNone (spec : type_of% @matchAt?_eq_none_iff) :
    WeakExcludedMiddle := weakExcludedMiddleOfForwardFailure (@matchAt?) spec

public theorem weakExcludedMiddleOfRevMatchAtNone (spec : type_of% @revMatchAt?_eq_none_iff) :
    WeakExcludedMiddle := weakExcludedMiddleOfBackwardFailure (@revMatchAt?) spec

end OmegaChecks.InitInventory.StringPatterns
