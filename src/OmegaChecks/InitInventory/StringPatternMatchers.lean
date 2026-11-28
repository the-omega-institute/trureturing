module
public import OmegaChecks.InitInventory.StringPatterns
public import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic

/-! Decidability of the pattern language is equivalent to having a lawful forward
or backward matcher. A query on a complete input tests whether the whole string
is in the language. Finite enumeration supplies the converse implementations.
The public success specifications give pointwise correspondence with the opaque
pinned selectors. For arbitrary languages the four existential statements below
are equivalent to excluded middle, which fails in the propositional model
`OmegaChecks.InitBoundaries.TwoWorlds.countermodel`. -/

namespace OmegaChecks.InitInventory.StringPatterns
open String.Slice.Pattern String.Slice.Pattern.Model

section
variable {ρ : Type} (pat : ρ) [PatternModel pat]

/-- A prefix matcher recognizes the whole input precisely when it returns its end. -/
@[instance_reducible] public def languageOfForward [ForwardPattern pat] [LawfulForwardPatternModel pat] :
    DecidablePred (PatternModel.Matches pat) := fun t =>
  decidable_of_iff (ForwardPattern.skipPrefix? pat t.toSlice = some t.toSlice.endPos) (by
    refine (LawfulForwardPatternModel.skipPrefix?_eq_some_iff _).trans ⟨fun h => ?_, fun h => ?_⟩
    · simpa only [String.Slice.sliceTo_endPos, String.copy_toSlice] using h.isMatch.matches_copy
    · exact ⟨⟨by simpa only [String.Slice.sliceTo_endPos, String.copy_toSlice] using h⟩,
        fun _ lt => (String.Slice.Pos.not_endPos_lt lt).elim⟩)

@[instance_reducible] public def languageOfBackward [BackwardPattern pat] [LawfulBackwardPatternModel pat] :
    DecidablePred (PatternModel.Matches pat) := fun t =>
  decidable_of_iff (BackwardPattern.skipSuffix? pat t.toSlice = some t.toSlice.startPos) (by
    refine (LawfulBackwardPatternModel.skipSuffix?_eq_some_iff _).trans ⟨fun h => ?_, fun h => ?_⟩
    · simpa only [String.Slice.sliceFrom_startPos, String.copy_toSlice] using h.isRevMatch.matches_copy
    · exact ⟨⟨by simpa only [String.Slice.sliceFrom_startPos, String.copy_toSlice] using h⟩,
        fun _ lt => (String.Slice.Pos.not_lt_startPos lt).elim⟩)

/-- Starting the finite search at the left boundary implements the full forward API. -/
@[implicit_reducible] public def forwardPattern [DecidablePred (PatternModel.Matches pat)] : ForwardPattern pat where
  skipPrefix? s := (forwardOfDecidable pat s.startPos).val

public theorem forwardLaw [DecidablePred (PatternModel.Matches pat)] :
    @LawfulForwardPatternModel _ pat (forwardPattern pat) _ := by
  letI := forwardPattern pat
  exact {
    skipPrefixOfNonempty?_eq := fun _ => rfl
    startsWith_eq := fun _ => rfl
    skipPrefix?_eq_some_iff := fun {s} pos =>
      ((forwardOfDecidable pat s.startPos).property pos).trans isLongestMatchAt_startPos_iff
  }

@[implicit_reducible] public def backwardPattern [DecidablePred (PatternModel.Matches pat)] : BackwardPattern pat where
  skipSuffix? s := (backwardOfDecidable pat s.endPos).val

public theorem backwardLaw [DecidablePred (PatternModel.Matches pat)] :
    @LawfulBackwardPatternModel _ pat (backwardPattern pat) _ := by
  letI := backwardPattern pat
  exact {
    skipSuffixOfNonempty?_eq := fun _ => rfl
    endsWith_eq := fun _ => rfl
    skipSuffix?_eq_some_iff := fun {s} pos =>
      ((backwardOfDecidable pat s.endPos).property pos).trans isLongestRevMatchAt_endPos_iff
  }

end

public theorem forwardAgrees {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] [ForwardPattern pat] [LawfulForwardPatternModel pat]
    {s : String.Slice} (a : s.Pos) : (forwardOfDecidable pat a).val = a.skip? pat :=
  Option.ext fun q => ((forwardOfDecidable pat a).property q).trans Pos.skip?_eq_some_iff.symm

public theorem backwardAgrees {ρ : Type} (pat : ρ) [PatternModel pat]
    [DecidablePred (PatternModel.Matches pat)] [BackwardPattern pat] [LawfulBackwardPatternModel pat]
    {s : String.Slice} (b : s.Pos) : (backwardOfDecidable pat b).val = b.revSkip? pat :=
  Option.ext fun q => ((backwardOfDecidable pat b).property q).trans Pos.revSkip?_eq_some_iff.symm

public theorem forwardPinned {ρ : Type} (pat : ρ) [PatternModel pat] [DecidablePred (PatternModel.Matches pat)]
    {s : String.Slice} (a : s.Pos) : (forwardOfDecidable pat a).val = matchAt? pat a :=
  Option.ext fun q => ((forwardOfDecidable pat a).property q).trans matchAt?_eq_some_iff.symm

public theorem backwardPinned {ρ : Type} (pat : ρ) [PatternModel pat] [DecidablePred (PatternModel.Matches pat)]
    {s : String.Slice} (b : s.Pos) : (backwardOfDecidable pat b).val = revMatchAt? pat b :=
  Option.ext fun q => ((backwardOfDecidable pat b).property q).trans revMatchAt?_eq_some_iff.symm

public theorem forwardLongestIff :
    (type_of% @IsMatch.exists_isLongestMatch) ↔ (∀ P : Prop, P ∨ ¬ P) := by
  refine ⟨excludedMiddleOfLongest, ?_⟩
  intro em ρ pat model s pos
  induction pos using WellFounded.induction String.Slice.Pos.wellFounded_gt with
  | h pos ih =>
    intro matchPos
    cases em (∃ pos', pos < pos' ∧ IsMatch pat pos') with
    | inl later =>
      obtain ⟨pos', lt, hit⟩ := later
      exact ih _ lt hit
    | inr last => exact ⟨pos, matchPos, fun q lt hit => last ⟨q, lt, hit⟩⟩

public theorem backwardLongestIff :
    (type_of% @IsRevMatch.exists_isLongestRevMatch) ↔ (∀ P : Prop, P ∨ ¬ P) := by
  refine ⟨excludedMiddleOfRevLongest, ?_⟩
  intro em ρ pat model s pos
  induction pos using WellFounded.induction String.Slice.Pos.wellFounded_lt with
  | h pos ih =>
    intro matchPos
    cases em (∃ pos', pos' < pos ∧ IsRevMatch pat pos') with
    | inl earlier =>
      obtain ⟨pos', lt, hit⟩ := earlier
      exact ih _ lt hit
    | inr first => exact ⟨pos, matchPos, fun q lt hit => first ⟨q, lt, hit⟩⟩

public theorem matchesAtIffEM :
    (type_of% @matchesAt_iff_exists_isMatch) ↔ (∀ P : Prop, P ∨ ¬ P) := by
  refine ⟨excludedMiddleOfMatchesAt, ?_⟩
  intro em ρ pat _ s pos
  refine ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestMatch_sliceFrom.isMatch⟩, fun ⟨p, hle, hit⟩ => ?_⟩
  obtain ⟨q, longest⟩ := (forwardLongestIff.mpr em) hit
  exact ⟨String.Slice.Pos.ofSliceFrom q, longest.isLongestMatchAt_ofSliceFrom⟩

public theorem revMatchesAtIffEM :
    (type_of% @revMatchesAt_iff_exists_isRevMatch) ↔ (∀ P : Prop, P ∨ ¬ P) := by
  refine ⟨excludedMiddleOfRevMatchesAt, ?_⟩
  intro em ρ pat _ s pos
  refine ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestRevMatch_sliceTo.isRevMatch⟩, fun ⟨p, hle, hit⟩ => ?_⟩
  obtain ⟨q, longest⟩ := (backwardLongestIff.mpr em) hit
  exact ⟨String.Slice.Pos.ofSliceTo q, longest.isLongestRevMatchAt_ofSliceTo⟩

end OmegaChecks.InitInventory.StringPatterns
