module
import all Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Lemmas.Pattern.String.Basic
import all Init.Data.String.Lemmas.Pattern.String.ForwardPattern
import all Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Lemmas.Pattern.Char
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.Lemmas.Pattern.Find.String
import all Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Monadic.Loop
import all OmegaChecks.InitPort.Alternatives.Array
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
public import OmegaChecks.InitPort.Alternatives.StringPattern.Encoding
public import OmegaChecks.InitPort.Alternatives.StringPattern.Models
import all OmegaChecks.InitPort.Alternatives.StringPattern.Models

/-! Forward and reverse string and slice searchers. -/

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

public theorem finitenessRelation._proof_2 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.ForwardSliceSearcher.finitenessRelation._proof_2) := by
  intro s it it' successor
  obtain ⟨step, next, valid⟩ := successor
  cases step
  all_goals try
    cases next
    revert valid
    obtain ⟨state⟩ := it
    cases state with
    | emptyBefore pos =>
      rintro (⟨_, advance⟩ | done)
      · change Option.lt _ it'.internalState.toOption _
        rw [advance]
        exact Prod.Lex.right _ (Nat.zero_lt_succ 0)
      · change Option.lt _ it'.internalState.toOption _
        rw [done]
        exact True.intro
    | emptyAt pos h =>
      rintro ⟨newPos, lt, advance⟩
      change Option.lt _ it'.internalState.toOption _
      rw [advance]
      exact Prod.Lex.left _ _ ((_root_.String.Slice.Pos.lt_iff_remainingBytes_lt ..).mp lt)
    | proper needle table ht stackPos needlePos hn =>
      rintro (⟨sp, np, _, advance, (lt | ⟨rfl, lt⟩)⟩ | done)
      · change Option.lt _ it'.internalState.toOption _
        rw [advance]
        exact Prod.Lex.left _ _ lt
      · change Option.lt _ it'.internalState.toOption _
        rw [advance]
        exact Prod.Lex.right _ lt
      · change Option.lt _ it'.internalState.toOption _
        rw [done]
        exact True.intro
    | atEnd => exact False.elim
  cases next

@[instance_reducible] public noncomputable def instIteratorLoopIdSearchStep :
    type_of% @_root_.String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep :=
  fun {_} => finiteIteratorLoop

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

private theorem prefixBytes {pat text : String} (bound : pat.utf8ByteSize ≤ text.utf8ByteSize) :
    text.toByteArray.extract 0 pat.utf8ByteSize = pat.toByteArray ↔ ∃ suffix, text = pat ++ suffix := by
  constructor
  · intro bytes
    have valid := _root_.String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero.mpr
      (show pat.rawEndPos ≤ text.rawEndPos ∧ (text.toByteArray.extract 0 pat.rawEndPos.byteIdx).IsValidUTF8
        from ⟨bound, bytes ▸ pat.isValidUTF8⟩)
    let pos := text.pos pat.rawEndPos valid
    have first : (text.sliceTo pos).copy = pat :=
      String.toByteArray_inj.mp (_root_.String.copy_toByteArray_sliceTo.trans bytes)
    exact ⟨_, (congrArg (fun t => t ++ _) first) ▸ pos.splits.eq_append⟩
  · rintro ⟨suffix, rfl⟩
    rw [String.toByteArray_append]
    exact ByteArray.extract_append_eq_left rfl

public theorem startsWith_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff) := by
  intro pat s
  unfold _root_.String.Slice.Pattern.ForwardSliceSearcher.startsWith
  split
  next bound =>
    apply _root_.String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff.trans
    change s.copy.toByteArray.extract 0 (0 + pat.utf8ByteSize) =
        pat.copy.toByteArray.extract 0 (0 + pat.utf8ByteSize) ↔ _
    rw [Nat.zero_add, ← _root_.String.Slice.utf8ByteSize_copy, ← String.size_toByteArray,
      ByteArray.extract_zero_size]
    apply prefixBytes
    rwa [_root_.String.Slice.utf8ByteSize_copy, _root_.String.Slice.utf8ByteSize_copy]
  next tooLong =>
    refine ⟨(fun eq => nomatch eq), fun ⟨suffix, eq⟩ => (tooLong ?_).elim⟩
    have bound : pat.copy.utf8ByteSize ≤ s.copy.utf8ByteSize := by
      rw [eq, String.utf8ByteSize_append]
      exact Nat.le_add_right ..
    rwa [_root_.String.Slice.utf8ByteSize_copy, _root_.String.Slice.utf8ByteSize_copy] at bound

public theorem skipPrefix?_eq_some_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_eq_some_iff) := by
  intro pat s pos
  unfold _root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?
  split
  next found =>
    obtain ⟨suffix, full⟩ := (_root_.String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff).mp found
    have valid : pat.rawEndPos.IsValidForSlice s := _root_.String.Pos.Raw.isValidForSlice_iff_exists_append.mpr
      ⟨pat.copy, suffix, full, _root_.String.Slice.rawEndPos_copy.symm⟩
    have h : (s.pos _ valid).Splits pat.copy suffix := ⟨full, _root_.String.Slice.rawEndPos_copy.symm⟩
    rw [_root_.String.Slice.offset_startPos, _root_.String.Pos.Raw.offsetBy_zero, _root_.String.Slice.pos!_eq_pos valid]
    exact ⟨fun eq => (Option.some.inj eq) ▸ h.copy_sliceTo_eq, fun eq => congrArg some (h.pos_eq (eq ▸ pos.splits))⟩
  next miss =>
    exact ⟨(fun eq => nomatch eq), fun eq => (miss ((_root_.String.Slice.Pattern.ForwardSliceSearcher.startsWith_iff).mpr ⟨_, eq ▸ pos.splits.eq_append⟩)).elim⟩

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.BackwardSliceSearcher

public theorem skipSuffix?_eq_some_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_eq_some_iff) := by
  intro pat s pos
  unfold _root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?
  split
  next found =>
    obtain ⟨before, full⟩ := (_root_.String.Slice.Pattern.BackwardSliceSearcher.endsWith_iff).mp found
    have size := congrArg String.utf8ByteSize full
    rw [String.utf8ByteSize_append, _root_.String.Slice.utf8ByteSize_copy, _root_.String.Slice.utf8ByteSize_copy] at size
    have offset : s.endPos.offset.unoffsetBy pat.rawEndPos = before.rawEndPos := by
      apply String.Pos.Raw.ext
      change s.utf8ByteSize - pat.utf8ByteSize = before.utf8ByteSize
      rw [size, Nat.add_sub_cancel]
    have valid := _root_.String.Pos.Raw.isValidForSlice_iff_exists_append.mpr ⟨before, pat.copy, full, offset⟩
    have h : (s.pos _ valid).Splits before pat.copy := ⟨full, offset⟩
    rw [_root_.String.Slice.pos!_eq_pos valid]
    exact ⟨fun eq => (Option.some.inj eq) ▸ h.copy_sliceFrom_eq,
      fun eq => congrArg some (h.pos_eq_of_eq_right (eq ▸ pos.splits))⟩
  next miss =>
    exact ⟨(fun eq => nomatch eq), fun eq => (miss ((_root_.String.Slice.Pattern.BackwardSliceSearcher.endsWith_iff).mpr
      ⟨_, eq ▸ pos.splits.eq_append⟩)).elim⟩

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.BackwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

public theorem skipPrefix?_of_isEmpty : type_of% @_root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_of_isEmpty := by
  intro pat s empty
  exact (_root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_eq_some_iff).mpr
    (_root_.String.Slice.copy_sliceTo_startPos.trans (_root_.String.Slice.copy_eq_empty_iff.mpr empty).symm)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem instLawfulForwardPatternModel : type_of% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.instLawfulForwardPatternModel := by
  intro pat
  refine {
    skipPrefixOfNonempty?_eq := fun _ => rfl
    startsWith_eq := fun _ => (_root_.String.Slice.Pattern.ForwardSliceSearcher.isSome_skipPrefix?).symm
    skipPrefix?_eq_some_iff := fun pos => ?_ }
  apply (_root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_eq_some_iff).trans
  exact _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatch_iff.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardStringSearcher

public theorem instLawfulForwardPatternModel : type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.instLawfulForwardPatternModel := by
  intro pat
  refine {
    skipPrefixOfNonempty?_eq := fun _ => rfl
    startsWith_eq := fun _ => (_root_.String.Slice.Pattern.ForwardSliceSearcher.isSome_skipPrefix?).symm
    skipPrefix?_eq_some_iff := fun pos => ?_ }
  apply (_root_.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_eq_some_iff).trans
  rw [_root_.String.copy_toSlice]
  exact _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatch_iff.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardStringSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.BackwardSliceSearcher

public theorem skipSuffix?_of_isEmpty : type_of% @_root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_of_isEmpty := by
  intro pat s empty
  exact (_root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_eq_some_iff).mpr
    (_root_.String.Slice.copy_sliceFrom_endPos.trans (_root_.String.Slice.copy_eq_empty_iff.mpr empty).symm)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.BackwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.BackwardSliceSearcher

public theorem instLawfulBackwardPatternModel : type_of% @_root_.String.Slice.Pattern.Model.BackwardSliceSearcher.instLawfulBackwardPatternModel := by
  intro pat
  refine {
    skipSuffixOfNonempty?_eq := fun _ => rfl
    endsWith_eq := fun _ => (_root_.String.Slice.Pattern.BackwardSliceSearcher.isSome_skipSuffix?).symm
    skipSuffix?_eq_some_iff := fun pos => ?_ }
  apply (_root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_eq_some_iff).trans
  exact _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestRevMatch_iff.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.BackwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.BackwardStringSearcher

public theorem instLawfulBackwardPatternModel : type_of% @_root_.String.Slice.Pattern.Model.BackwardStringSearcher.instLawfulBackwardPatternModel := by
  intro pat
  refine {
    skipSuffixOfNonempty?_eq := fun _ => rfl
    endsWith_eq := fun _ => (_root_.String.Slice.Pattern.BackwardSliceSearcher.isSome_skipSuffix?).symm
    skipSuffix?_eq_some_iff := fun pos => ?_ }
  apply (_root_.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_eq_some_iff).trans
  rw [_root_.String.copy_toSlice]
  exact _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatch_iff.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.BackwardStringSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model
open _root_.String.Slice _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model

public theorem LawfulToForwardSearcherModel.defaultImplementation :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulToForwardSearcherModel.defaultImplementation := by
  intro ρ pat _ _ _ _
  let inst : ToForwardSearcher pat (ToForwardSearcher.DefaultForwardSearcher pat) := .defaultImplementation
  refine ⟨fun s => ?_⟩
  suffices ∀ pos : s.Pos, IsValidSearchFrom pat pos
      (_root_.Std.Iter.mk (α := ToForwardSearcher.DefaultForwardSearcher pat s) ⟨pos⟩).toList from
    this s.startPos
  intro pos
  induction pos using WellFounded.induction Pos.wellFounded_gt with
  | h pos ih =>
    rw [_root_.Std.Iter.toList_eq_match_step]
    dsimp only [_root_.Std.Iter.step, _root_.Std.IterM.step, _root_.Std.Iterator.step,
      _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    by_cases stop : pos = s.endPos
    · subst pos
      rw [dite_eq_left rfl, Id.run_pure, Std.Shrink.inflate_deflate]
      exact .endPos
    · rw [dite_eq_right stop]
      split <;> rename_i stepEq
      · split at stepEq <;> rename_i found
        · rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq
          cases stepEq
          refine IsValidSearchFrom.matched ?_ (ih _ ?_)
          · rw [LawfulForwardPattern.skipPrefixOfNonempty?_eq,
              LawfulForwardPatternModel.skipPrefix?_eq_some_iff] at found
            exact found.isLongestMatchAt_ofSliceFrom
          · exact Nat.lt_of_le_of_lt (Pos.le_ofSliceFrom (pos := (s.sliceFrom pos).startPos))
              (Pos.ofSliceFrom_lt_ofSliceFrom_iff.mpr
                ((Pos.startPos_lt_iff _).mpr (StrictForwardPattern.ne_startPos _ _ found)))
        · rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq
          cases stepEq
          refine IsValidSearchFrom.mismatched Pos.lt_next ?_ (ih _ Pos.lt_next)
          intro cursor lo hi
          have same : pos = cursor := Pos.ext (String.Pos.Raw.ext
            (Nat.le_antisymm lo (Pos.lt_next_iff_le.mp hi)))
          subst cursor
          rw [LawfulForwardPattern.skipPrefixOfNonempty?_eq] at found
          exact LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff.mp found
      · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq
      · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq

public theorem LawfulToBackwardSearcherModel.defaultImplementation :
    type_of% @_root_.String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.defaultImplementation := by
  intro ρ pat _ _ _ _
  let inst : ToBackwardSearcher pat (ToBackwardSearcher.DefaultBackwardSearcher pat) := .defaultImplementation
  refine ⟨fun s => ?_⟩
  suffices ∀ pos : s.Pos, IsValidRevSearchFrom pat pos
      (_root_.Std.Iter.mk (α := ToBackwardSearcher.DefaultBackwardSearcher pat s) ⟨pos⟩).toList from
    this s.endPos
  intro pos
  induction pos using WellFounded.induction Pos.wellFounded_lt with
  | h pos ih =>
    rw [_root_.Std.Iter.toList_eq_match_step]
    dsimp only [_root_.Std.Iter.step, _root_.Std.IterM.step, _root_.Std.Iterator.step,
      _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    by_cases stop : pos = s.startPos
    · subst pos
      rw [dite_eq_left rfl, Id.run_pure, Std.Shrink.inflate_deflate]
      exact .startPos
    · rw [dite_eq_right stop]
      split <;> rename_i stepEq
      · split at stepEq <;> rename_i found
        · rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq
          cases stepEq
          refine IsValidRevSearchFrom.matched ?_ (ih _ ?_)
          · rw [LawfulBackwardPattern.skipSuffixOfNonempty?_eq,
              LawfulBackwardPatternModel.skipSuffix?_eq_some_iff] at found
            exact found.isLongestRevMatchAt_ofSliceTo
          · exact Nat.lt_of_lt_of_le (Pos.ofSliceTo_lt_ofSliceTo_iff.mpr
                ((Pos.lt_endPos_iff _).mpr (StrictBackwardPattern.ne_endPos _ _ found)))
              (Pos.ofSliceTo_le (pos := (s.sliceTo pos).endPos))
        · rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq
          cases stepEq
          refine IsValidRevSearchFrom.mismatched Pos.prev_lt ?_ (ih _ Pos.prev_lt)
          intro cursor lo hi
          have same : pos = cursor := Pos.ext (String.Pos.Raw.ext
            (Nat.le_antisymm (Pos.prev_lt_iff_le.mp lo) hi))
          subst cursor
          rw [LawfulBackwardPattern.skipSuffixOfNonempty?_eq] at found
          exact LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff.mp found
      · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq
      · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher
open _root_.String.Slice _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem toList_emptyBefore_eq :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.toList_emptyBefore_eq := by
  intro s pos
  rw [_root_.Std.Iter.toList_eq_match_step]
  dsimp only [_root_.Std.Iter.step, _root_.Std.IterM.step, _root_.Std.Iterator.step,
    _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
  by_cases stop : pos = s.endPos
  · rw [dite_eq_left stop, dite_eq_right (fun h => h stop), Id.run_pure, Std.Shrink.inflate_deflate]
    exact congrArg (List.cons _) _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.toList_atEnd_eq
  · rw [dite_eq_right stop, dite_eq_left stop, Id.run_pure, Std.Shrink.inflate_deflate]
    rfl

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.CharPred.Decidable

public theorem instLawfulToBackwardSearcherModelForallCharPropDefaultBackwardSearcherForallBoolDecide :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.Decidable.instLawfulToBackwardSearcherModelForallCharPropDefaultBackwardSearcherForallBoolDecide := by
  intro p _
  refine ⟨fun s => ?_⟩
  exact (_root_.String.Slice.Pattern.Model.CharPred.Decidable.isValidRevSearchFrom_iff_isValidRevSearchFrom_decide).mpr
    (_root_.String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList
      (pat := (fun c => decide (p c))) s)


public theorem instLawfulToForwardSearcherModelForallCharPropDefaultForwardSearcherForallBoolDecide :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.Decidable.instLawfulToForwardSearcherModelForallCharPropDefaultForwardSearcherForallBoolDecide := by
  intro p _
  refine ⟨fun s => ?_⟩
  exact (_root_.String.Slice.Pattern.Model.CharPred.Decidable.isValidSearchFrom_iff_isValidSearchFrom_decide).mpr
    (_root_.String.Slice.Pattern.Model.LawfulToForwardSearcherModel.isValidSearchFrom_toList
      (pat := (fun c => decide (p c))) s)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.CharPred.Decidable

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.Char

public theorem instLawfulToForwardSearcherModelCharDefaultForwardSearcherForallBoolBeq :
    type_of% @_root_.String.Slice.Pattern.Model.Char.instLawfulToForwardSearcherModelCharDefaultForwardSearcherForallBoolBeq := by
  intro c
  refine ⟨fun s => ?_⟩
  exact (_root_.String.Slice.Pattern.Model.Char.isValidSearchFrom_iff_isValidSearchFrom_beq).mpr
    (_root_.String.Slice.Pattern.Model.LawfulToForwardSearcherModel.isValidSearchFrom_toList
      (pat := (· == c)) s)


public theorem instLawfulToBackwardSearcherModelCharDefaultBackwardSearcherForallBoolBeq :
    type_of% @_root_.String.Slice.Pattern.Model.Char.instLawfulToBackwardSearcherModelCharDefaultBackwardSearcherForallBoolBeq := by
  intro c
  refine ⟨fun s => ?_⟩
  exact (_root_.String.Slice.Pattern.Model.Char.isValidRevSearchFrom_iff_isValidRevSearchFrom_beq).mpr
    (_root_.String.Slice.Pattern.Model.LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList
      (pat := (· == c)) s)

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.Char
