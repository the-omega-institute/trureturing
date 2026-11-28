module
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Lemmas.Pattern.Split.Basic
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

/-- The result of a forward matcher supplies a decision for every proposition. -/
public def decidableOfForwardResult (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat a = some b ↔ IsLongestMatchAt pat a b) (P : Prop) : Decidable P := by
  letI : PatternModel () := accepts P
  cases result : find () sample.startPos with
  | some q => exact isTrue ((correct.mp result).isLongestMatch_sliceFrom.isMatch.matches_copy)
  | none =>
    apply isFalse
    intro yes
    have clash := result.symm.trans (correct.mpr (matchesWhole P yes))
    cases clash

/-- The successful-result specification of any reverse matcher decides every proposition. -/
public def decidableOfBackwardResult (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat b = some a ↔ IsLongestRevMatchAt pat a b) (P : Prop) : Decidable P := by
  letI : PatternModel () := accepts P
  cases result : find () sample.endPos with
  | some q => exact isTrue ((correct.mp result).isLongestRevMatch_sliceTo.isRevMatch.matches_copy)
  | none =>
    apply isFalse
    intro yes
    have clash := result.symm.trans (correct.mpr (revMatchesWhole P yes))
    cases clash


private def positions (s : String.Slice) : List s.Pos :=
  s.endPos :: (String.Slice.Model.positionsFrom s.startPos).map Subtype.val

private theorem mem_positions {s : String.Slice} (q : s.Pos) : q ∈ positions s := by
  by_cases h : q = s.endPos
  · exact h ▸ .head _
  · exact .tail _ (List.mem_map.mpr ⟨⟨q, h⟩, String.Slice.Model.mem_positionsFrom_startPos, rfl⟩)

private def selectPosition {s : String.Slice} (p : s.Pos → Prop) (test : DecidablePred p) : Option s.Pos :=
  (positions s).find? (fun q => @decide (p q) (test q))

private theorem selectPosition_spec {s : String.Slice} (p : s.Pos → Prop) (test : DecidablePred p)
    (unique : ∀ {a b}, p a → p b → a = b) (q : s.Pos) :
    selectPosition p test = some q ↔ p q := by
  letI := test
  unfold selectPosition
  constructor
  · intro found
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
  · intro hit
    cases result : (positions s).find? (fun x => decide (p x)) with
    | none => exact False.elim ((List.find?_eq_none.mp result q (mem_positions q)) (decide_eq_true hit))
    | some r =>
      exact congrArg some (unique (of_decide_eq_true (List.find?_eq_some_iff_append.mp result).1) hit)

private def allPositions {s : String.Slice} (p : s.Pos → Prop) [DecidablePred p] :
    Decidable (∀ q, p q) :=
  decidable_of_iff (∀ q ∈ positions s, p q)
    ⟨fun h q => h q (mem_positions q), fun h q _ => h q⟩

private def longestAtDecision {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] {s : String.Slice} (a b : s.Pos) :
    Decidable (IsLongestMatchAt pat a b) := by
  by_cases h : a ≤ b
  · let t := s.sliceFrom a
    let z : t.Pos := a.sliceFrom b h
    letI (q : t.Pos) : Decidable (IsMatch pat q) := decidable_of_iff _ isMatch_iff.symm
    letI := allPositions (s := t) (fun q => z < q → ¬ IsMatch pat q)
    letI : Decidable (IsLongestMatch pat z) := decidable_of_iff _ isLongestMatch_iff.symm
    exact decidable_of_iff (IsLongestMatch pat z)
      ⟨fun m => ⟨h, m⟩, fun m => m.isLongestMatch_sliceFrom⟩
  · exact isFalse fun m => h m.le

private def revLongestAtDecision {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] {s : String.Slice} (a b : s.Pos) :
    Decidable (IsLongestRevMatchAt pat a b) := by
  by_cases h : a ≤ b
  · let t := s.sliceTo b
    let z : t.Pos := b.sliceTo a h
    letI (q : t.Pos) : Decidable (IsRevMatch pat q) := decidable_of_iff _ isRevMatch_iff.symm
    letI := allPositions (s := t) (fun q => q < z → ¬ IsRevMatch pat q)
    letI : Decidable (IsLongestRevMatch pat z) := decidable_of_iff _ isLongestRevMatch_iff.symm
    exact decidable_of_iff (IsLongestRevMatch pat z)
      ⟨fun m => ⟨h, m⟩, fun m => m.isLongestRevMatch_sliceTo⟩
  · exact isFalse fun m => h m.le

/-- Decidability of this pattern's language suffices to select its longest forward matches. -/
public def forwardOfDecidable {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] {s : String.Slice} (a : s.Pos) :
    {result : Option s.Pos // ∀ b, result = some b ↔ IsLongestMatchAt pat a b} :=
  ⟨selectPosition _ (longestAtDecision pat a),
   selectPosition_spec _ _ (fun h k => h.eq k)⟩

/-- A decidable pattern language also suffices for longest reverse matches. -/
public def backwardOfDecidable {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] {s : String.Slice} (b : s.Pos) :
    {result : Option s.Pos // ∀ a, result = some a ↔ IsLongestRevMatchAt pat a b} :=
  ⟨selectPosition _ (fun a => revLongestAtDecision pat a b),
   selectPosition_spec _ _ (fun h k => h.eq k)⟩

public theorem excludedMiddleOfForwardResult (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat a = some b ↔ IsLongestMatchAt pat a b) (P : Prop) : P ∨ ¬ P :=
  @Decidable.em P (decidableOfForwardResult find correct P)

public theorem excludedMiddleOfBackwardResult (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a b : s.Pos},
      find pat b = some a ↔ IsLongestRevMatchAt pat a b) (P : Prop) : P ∨ ¬ P :=
  @Decidable.em P (decidableOfBackwardResult find correct P)

public theorem excludedMiddleOfMatchAtSome (spec : type_of% @matchAt?_eq_some_iff) :
    ∀ P : Prop, P ∨ ¬ P := excludedMiddleOfForwardResult (@matchAt?) spec

public theorem excludedMiddleOfRevMatchAtSome (spec : type_of% @revMatchAt?_eq_some_iff) :
    ∀ P : Prop, P ∨ ¬ P := excludedMiddleOfBackwardResult (@revMatchAt?) spec

/-- Weak excluded middle decides the negation of each proposition. -/
public def WeakExcludedMiddle : Prop := ∀ P : Prop, ¬ P ∨ ¬ ¬ P

public def decidableNegOfForwardFailure (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a : s.Pos},
      find pat a = none ↔ ¬ MatchesAt pat a) (P : Prop) : Decidable (¬ P) := by
  letI : PatternModel () := accepts P
  cases result : find () sample.startPos with
  | none => exact isTrue fun yes => correct.mp result ⟨⟨_, matchesWhole P yes⟩⟩
  | some q =>
    apply isFalse
    intro no
    have absent : ¬ MatchesAt () sample.startPos := by
      rintro ⟨⟨_, hit⟩⟩
      exact no hit.isLongestMatch_sliceFrom.isMatch.matches_copy
    cases result.symm.trans (correct.mpr absent)

public theorem weakExcludedMiddleOfForwardFailure (find : type_of% @matchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {a : s.Pos},
      find pat a = none ↔ ¬ MatchesAt pat a) : WeakExcludedMiddle := fun P =>
  @Decidable.em (¬ P) (decidableNegOfForwardFailure find correct P)

public def decidableNegOfBackwardFailure (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {b : s.Pos},
      find pat b = none ↔ ¬ RevMatchesAt pat b) (P : Prop) : Decidable (¬ P) := by
  letI : PatternModel () := accepts P
  cases result : find () sample.endPos with
  | none => exact isTrue fun yes => correct.mp result ⟨⟨_, revMatchesWhole P yes⟩⟩
  | some q =>
    apply isFalse
    intro no
    have absent : ¬ RevMatchesAt () sample.endPos := by
      rintro ⟨⟨_, hit⟩⟩
      exact no hit.isLongestRevMatch_sliceTo.isRevMatch.matches_copy
    cases result.symm.trans (correct.mpr absent)

public theorem weakExcludedMiddleOfBackwardFailure (find : type_of% @revMatchAt?)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] {s : String.Slice} {b : s.Pos},
      find pat b = none ↔ ¬ RevMatchesAt pat b) : WeakExcludedMiddle := fun P =>
  @Decidable.em (¬ P) (decidableNegOfBackwardFailure find correct P)

public theorem weakExcludedMiddleOfMatchAtNone (spec : type_of% @matchAt?_eq_none_iff) :
    WeakExcludedMiddle := weakExcludedMiddleOfForwardFailure (@matchAt?) spec

public theorem weakExcludedMiddleOfRevMatchAtNone (spec : type_of% @revMatchAt?_eq_none_iff) :
    WeakExcludedMiddle := weakExcludedMiddleOfBackwardFailure (@revMatchAt?) spec

@[instance_reducible] private def nonemptyWhen (P : Prop) : PatternModel () :=
  ⟨fun t => t ≠ "" ∧ P⟩

/-- A faithful forward result decides any proposition even when matching is restricted to strict models. -/
public def decidableOfStrictForwardResult
    (find : ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice}, s.Pos → Option s.Pos)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} {a b : s.Pos}, find pat a = some b ↔ IsLongestMatchAt pat a b)
    (P : Prop) : Decidable P := by
  letI : PatternModel () := nonemptyWhen P
  letI : StrictPatternModel () := ⟨fun h => h.1 rfl⟩
  cases result : find () sample.startPos with
  | some q => exact isTrue (correct.mp result).isLongestMatch_sliceFrom.isMatch.matches_copy.2
  | none =>
    apply isFalse
    intro yes
    have hit : IsLongestMatchAt () sample.startPos sample.endPos :=
      isLongestMatchAt_startPos_iff.mpr ⟨⟨⟨by decide, yes⟩⟩, fun q beyond _ =>
        Nat.not_lt_of_ge q.isValidForSlice.le_utf8ByteSize beyond⟩
    cases result.symm.trans (correct.mpr hit)

/-- A faithful reverse result for strict models also decides any proposition. -/
public def decidableOfStrictBackwardResult
    (find : ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice}, s.Pos → Option s.Pos)
    (correct : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} {a b : s.Pos}, find pat b = some a ↔ IsLongestRevMatchAt pat a b)
    (P : Prop) : Decidable P := by
  letI : PatternModel () := nonemptyWhen P
  letI : StrictPatternModel () := ⟨fun h => h.1 rfl⟩
  cases result : find () sample.endPos with
  | some q => exact isTrue (correct.mp result).isLongestRevMatch_sliceTo.isRevMatch.matches_copy.2
  | none =>
    apply isFalse
    intro yes
    have hit : IsLongestRevMatchAt () sample.startPos sample.endPos :=
      isLongestRevMatchAt_endPos_iff.mpr ⟨⟨⟨by decide, yes⟩⟩, fun _ before _ =>
        Nat.not_lt_zero _ before⟩
    cases result.symm.trans (correct.mpr hit)

/-- On a one-character slice, an arbitrary strict model can encode an undecided proposition.
The three split equations distinguish a successful match from a completely rejected slice. -/
public theorem weakExcludedMiddleOfSplit
    (split : type_of% @String.Slice.Pattern.Model.split)
    (atEnd : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} {first : s.Pos}, split pat first s.endPos (String.Slice.Pos.le_endPos _) =
        [s.subslice first s.endPos (String.Slice.Pos.le_endPos _)])
    (onMatch : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} {first start stop : s.Pos} {hle}, IsLongestMatchAt pat start stop →
        split pat first start hle = s.subslice first start hle :: split pat stop stop (Nat.le_refl _))
    (onMiss : ∀ {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} {first start : s.Pos} (stop : s.Pos) (hle : start ≤ stop) {hfirst}
      (_ : ∀ p, start ≤ p → p < stop → ¬ MatchesAt pat p),
        split pat first start hfirst = split pat first stop (Nat.le_trans hfirst hle)) :
    WeakExcludedMiddle := by
  intro P
  letI : PatternModel () := nonemptyWhen P
  letI : StrictPatternModel () := ⟨fun h => h.1 rfl⟩
  let parts := split () sample.startPos sample.startPos (Nat.le_refl _)
  have resultOnMatch (yes : P) : parts.length = 2 := by
    have hit : IsLongestMatchAt () sample.startPos sample.endPos := by
      apply isLongestMatchAt_startPos_iff.mpr
      exact ⟨⟨⟨by decide, yes⟩⟩, fun q beyond _ =>
        Nat.not_lt_of_ge q.isValidForSlice.le_utf8ByteSize beyond⟩
    exact (congrArg List.length (onMatch (first := sample.startPos) hit)).trans
      (congrArg (fun t : List sample.Subslice => t.length.succ) (atEnd (pat := ()) (first := sample.endPos)))
  have resultOnMiss (no : ¬ P) : parts.length = 1 := by
    have miss (q : sample.Pos) : ¬ MatchesAt () q := by
      rintro ⟨⟨_, hit⟩⟩
      exact no hit.isLongestMatch_sliceFrom.isMatch.matches_copy.2
    exact congrArg List.length ((onMiss sample.endPos (String.Slice.Pos.startPos_le _) (fun q _ _ => miss q)).trans atEnd)
  by_cases two : parts.length = 2
  · exact Or.inr fun no => (by decide : (1 : Nat) ≠ 2) ((resultOnMiss no).symm.trans two)
  · exact Or.inl fun yes => two (resultOnMatch yes)

public theorem weakExcludedMiddleOfOfficialSplit
    (split : type_of% @String.Slice.Pattern.Model.split)
    (agreement : ∀ {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
      {s : String.Slice} (first start : s.Pos) (hle : first ≤ start),
      split pat first start hle = String.Slice.Pattern.Model.split pat first start hle) :
    WeakExcludedMiddle := by
  apply weakExcludedMiddleOfSplit split
  · intros; exact (agreement ..).trans split_endPos
  · intros; exact (agreement ..).trans ((split_eq_of_isLongestMatchAt ‹_›).trans
      (congrArg (List.cons _) (agreement ..).symm))
  · intros; exact (agreement ..).trans ((split_eq_of_not_matchesAt _ ‹_› ‹_›).trans (agreement ..).symm)

end OmegaChecks.InitInventory.StringPatterns
