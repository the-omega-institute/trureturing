module
import all Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Lemmas.Pattern.String.Basic
import all Init.Data.String.Lemmas.Pattern.String.ForwardPattern
import all Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
import all Init.Data.String.Basic
import all Init.Data.String.Lemmas.Pattern.Char
import all Init.Data.String.Lemmas.Pattern.Pred
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all OmegaChecks.InitPort.Alternatives.Array
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
public import OmegaChecks.InitPort.Alternatives.StringEncoding

/-! UTF-8 byte comparisons, search traces and character predicate patterns. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem String.Slice.mem_toList_copy_iff_exists_get :
    type_of% @_root_.String.Slice.mem_toList_copy_iff_exists_get := by
  intro s c
  constructor
  · intro mem
    obtain ⟨before, after, eq⟩ := List.mem_iff_append.mp mem
    have split : s.copy = String.ofList before ++ (String.singleton c ++ String.ofList after) := by
      apply _root_.String.toList_inj.mp
      simpa only [String.toList_append, String.toList_ofList, String.toList_singleton, List.singleton_append] using eq
    have valid := _root_.String.Pos.Raw.isValidForSlice_iff_exists_append.mpr
      (show ∃ a b, s.copy = a ++ b ∧ (String.ofList before).rawEndPos = a.rawEndPos from ⟨_, _, split, rfl⟩)
    let pos := s.pos (String.ofList before).rawEndPos valid
    have parts : pos.Splits (String.ofList before) (String.singleton c ++ String.ofList after) := ⟨split, rfl⟩
    exact ⟨pos, parts.ne_endPos_of_singleton, parts.next.get_eq_of_singleton⟩
  · rintro ⟨pos, h, rfl⟩
    apply List.mem_iff_append.mpr
    refine ⟨(s.sliceTo pos).copy.toList, (s.sliceFrom (pos.next h)).copy.toList, ?_⟩
    have eq := congrArg String.toList (pos.splits_next_right h).eq_append
    simpa only [String.toList_append, String.toList_singleton, List.singleton_append] using eq

end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

open _root_.String.Slice.Pattern.Model

private theorem forwardSearch {α β : Type} {p : α} {q : β} [PatternModel p] [PatternModel q]
    {s : String.Slice} {pos : s.Pos} {steps}
    (same : ∀ {a b : s.Pos}, IsLongestMatchAt p a b ↔ IsLongestMatchAt q a b) :
    IsValidSearchFrom p pos steps → IsValidSearchFrom q pos steps := by
  intro search
  induction search with
  | endPos => exact .endPos
  | matched h _ tail => exact .matched (same.mp h) tail
  | mismatched lt miss _ tail =>
    refine .mismatched lt (fun cursor lo hi found => miss cursor lo hi ?_) tail
    obtain ⟨⟨w, matched⟩⟩ := found
    exact ⟨⟨w, same.mpr matched⟩⟩

private theorem reverseSearch {α β : Type} {p : α} {q : β} [PatternModel p] [PatternModel q]
    {s : String.Slice} {pos : s.Pos} {steps}
    (same : ∀ {a b : s.Pos}, IsLongestRevMatchAt p a b ↔ IsLongestRevMatchAt q a b) :
    IsValidRevSearchFrom p pos steps → IsValidRevSearchFrom q pos steps := by
  intro search
  induction search with
  | startPos => exact .startPos
  | matched h _ tail => exact .matched (same.mp h) tail
  | mismatched lt miss _ tail =>
    refine .mismatched lt (fun cursor lo hi found => miss cursor lo hi ?_) tail
    obtain ⟨⟨w, matched⟩⟩ := found
    exact ⟨⟨w, same.mpr matched⟩⟩

namespace ForwardSliceSearcher

private theorem bytesInWindow {pat text : ByteArray} {off : Nat} (bound : off + pat.size ≤ text.size) :
    text.extract off (off + pat.size) = pat ↔
      ∀ (i) (hi : i < pat.size), pat[i] = text[off + i] := by
  have size : (text.extract off (off + pat.size)).size = pat.size :=
    ByteArray.size_extract.trans ((congrArg (· - off) (Nat.min_eq_left bound)).trans (Nat.add_sub_cancel_left ..))
  constructor
  · intro eq i hi
    have inside := Nat.lt_of_lt_of_eq hi size.symm
    have atIndex : pat[i] = (text.extract off (off + pat.size))[i] := by
      generalize text.extract off (off + pat.size) = bs at eq inside ⊢
      cases eq
      rfl
    exact atIndex.trans (ByteArray.getElem_extract inside)
  · intro bytes
    exact ByteArray.ext_getElem size fun i hi hi' => (ByteArray.getElem_extract hi).trans (bytes i hi').symm

public theorem matchesAt_iff_getElem :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_getElem := by
  intro pat s pos nonempty
  have ps := pat.utf8ByteSize_eq_size_toByteArray_copy
  have ss := s.utf8ByteSize_eq_size_toByteArray_copy
  apply (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt nonempty).trans
  constructor
  · rintro ⟨valid, matched⟩
    have bound := valid.le_utf8ByteSize
    change pos.offset.byteIdx + pat.utf8ByteSize ≤ s.utf8ByteSize at bound
    rw [ps, ss] at bound
    refine ⟨bound, (bytesInWindow bound).mp ?_⟩
    have extracted := (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatchAt_iff_extract nonempty).mp matched
    change s.copy.toByteArray.extract pos.offset.byteIdx (pos.offset.byteIdx + pat.utf8ByteSize) = _ at extracted
    rwa [ps] at extracted
  · rintro ⟨bound, bytes⟩
    have extracted := (bytesInWindow bound).mpr bytes
    rw [← ps] at extracted bound
    have utf8 := extracted ▸ pat.copy.isValidUTF8
    have valid := (Alternatives.String.Pos.Raw.isValidUTF8_extract_iff (s := s.copy) pos.offset
      (pos.offset.increaseBy pat.utf8ByteSize) (Nat.le_add_right ..) bound).mp utf8
    have distinct : pos.offset ≠ pos.offset.increaseBy pat.utf8ByteSize := by
      intro eq
      have sizes := congrArg _root_.String.Pos.Raw.byteIdx eq
      have zero := Nat.add_left_cancel ((Nat.add_zero pos.offset.byteIdx).trans sizes)
      exact Bool.noConfusion (nonempty.symm.trans (_root_.String.Slice.isEmpty_iff.mpr zero.symm))
    refine ⟨_root_.String.Pos.Raw.isValid_copy_iff.mp ((valid.resolve_left distinct).2), ?_⟩
    exact (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.isLongestMatchAt_iff_extract nonempty).mpr extracted

public theorem le_of_matchesAt :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_of_matchesAt := by
  intro pat s pos nonempty matched
  have bound := ((matchesAt_iff_getElem nonempty).mp matched).1
  change pos.offset.byteIdx + pat.utf8ByteSize ≤ s.utf8ByteSize
  rwa [pat.utf8ByteSize_eq_size_toByteArray_copy, s.utf8ByteSize_eq_size_toByteArray_copy]

end ForwardSliceSearcher

namespace ForwardStringSearcher

private theorem toSliceNonempty {pat : String} (h : pat ≠ "") : pat.toSlice.isEmpty = false := by
  cases e : pat.toSlice.isEmpty with
  | false => rfl
  | true => exact (h (_root_.String.isEmpty_toSlice_iff.mp e)).elim

public theorem isValidSearchFrom_iff_isValidSearchFrom_toSlice :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.isValidSearchFrom_iff_isValidSearchFrom_toSlice := by
  intro pat s pos steps
  exact ⟨forwardSearch _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    forwardSearch _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice.symm⟩

public theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_toSlice :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.isValidRevSearchFrom_iff_isValidRevSearchFrom_toSlice := by
  intro pat s pos steps
  exact ⟨reverseSearch _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice,
    reverseSearch _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.symm⟩

public theorem matchesAt_iff_isLongestMatchAt :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_isLongestMatchAt := by
  intro pat s pos ne
  apply _root_.String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_toSlice.trans
  apply (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt (toSliceNonempty ne)).trans
  constructor
  · rintro ⟨h, matchAt⟩
    exact ⟨h, _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice.mpr matchAt⟩
  · rintro ⟨h, matchAt⟩
    exact ⟨h, _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestMatchAt_iff_isLongestMatchAt_toSlice.mp matchAt⟩

public theorem revMatchesAt_iff_isLongestRevMatchAt :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.revMatchesAt_iff_isLongestRevMatchAt := by
  intro pat s pos ne
  apply _root_.String.Slice.Pattern.Model.ForwardStringSearcher.revMatchesAt_iff_toSlice.trans
  apply (_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.revMatchesAt_iff_isLongestRevMatchAt (toSliceNonempty ne)).trans
  constructor
  · rintro ⟨h, matchAt⟩
    exact ⟨h, _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.mpr matchAt⟩
  · rintro ⟨h, matchAt⟩
    exact ⟨h, _root_.String.Slice.Pattern.Model.ForwardStringSearcher.isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.mp matchAt⟩

public theorem matchesAt_iff_getElem :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_getElem := by
  intro pat s pos ne
  apply _root_.String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_toSlice.trans
  apply (ForwardSliceSearcher.matchesAt_iff_getElem (toSliceNonempty ne)).trans
  let bytesMatch (p : String) : Prop :=
    ∃ (h : pos.offset.byteIdx + p.toByteArray.size ≤ s.copy.toByteArray.size),
      ∀ (j) (hj : j < p.toByteArray.size), p.toByteArray[j] = s.copy.toByteArray[pos.offset.byteIdx + j]
  exact Iff.of_eq (congrArg bytesMatch _root_.String.copy_toSlice)

public theorem le_of_matchesAt :
    type_of% @_root_.String.Slice.Pattern.Model.ForwardStringSearcher.le_of_matchesAt := by
  intro pat s pos ne matched
  exact ForwardSliceSearcher.le_of_matchesAt (toSliceNonempty ne)
    (_root_.String.Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_toSlice.mp matched)

end ForwardStringSearcher

namespace CharPred

open _root_.String.Slice in
public theorem isLongestMatchAtChain_iff :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.isLongestMatchAtChain_iff := by
  intro p s start stop
  constructor
  · intro chain
    induction chain with
    | nil => exact ⟨Nat.le_refl _, fun _ le lt => (Nat.not_lt_of_ge le lt).elim⟩
    | cons a b z matched tail ih =>
      obtain ⟨ne, rfl, accepted⟩ := _root_.String.Slice.Pattern.Model.CharPred.isLongestMatchAt_iff.mp matched
      refine ⟨Nat.le_trans Pos.le_next ih.1, fun cursor lower upper => ?_⟩
      obtain eq | lt := Nat.eq_or_lt_of_le lower
      · obtain rfl : a = cursor := Pos.ext (String.Pos.Raw.ext eq)
        exact accepted
      · exact ih.2 cursor (Pos.next_le_iff_lt.mpr lt) upper
  · induction start using WellFounded.induction Pos.wellFounded_gt with
    | h start ih =>
      rintro ⟨le, all⟩
      obtain eq | lt := Nat.eq_or_lt_of_le le
      · obtain rfl : start = stop := Pos.ext (String.Pos.Raw.ext eq)
        exact .nil _
      · have ne := Pos.ne_endPos_of_lt (show start < stop from lt)
        exact .cons _ (start.next ne) _
          (_root_.String.Slice.Pattern.Model.CharPred.isLongestMatchAt_iff.mpr ⟨ne, rfl, all start (Nat.le_refl _) lt⟩)
          (ih _ Pos.lt_next ⟨Pos.next_le_iff_lt.mpr lt, fun cursor lo hi => all cursor (Nat.le_trans Pos.le_next lo) hi⟩)

open _root_.String.Slice in
public theorem isLongestRevMatchAtChain_iff :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.isLongestRevMatchAtChain_iff := by
  intro p s start stop
  constructor
  · intro chain
    induction chain with
    | nil => exact ⟨Nat.le_refl _, fun _ le lt => (Nat.not_lt_of_ge le lt).elim⟩
    | cons b z tail matched ih =>
      obtain ⟨ne, rfl, accepted⟩ := _root_.String.Slice.Pattern.Model.CharPred.isLongestRevMatchAt_iff.mp matched
      refine ⟨Nat.le_trans ih.1 (Nat.le_of_lt Pos.prev_lt), fun cursor lower upper => ?_⟩
      obtain eq | lt := Nat.eq_or_lt_of_le (show cursor ≤ z.prev ne from Pos.le_prev_iff_lt.mpr upper)
      · obtain eq : cursor = z.prev ne := Pos.ext (String.Pos.Raw.ext eq)
        subst cursor
        exact accepted
      · exact ih.2 cursor lower lt
  · induction stop using WellFounded.induction Pos.wellFounded_lt with
    | h stop ih =>
      rintro ⟨le, all⟩
      obtain eq | lt := Nat.eq_or_lt_of_le le
      · obtain rfl : start = stop := Pos.ext (String.Pos.Raw.ext eq)
        exact .nil _
      · have ne := Pos.ne_startPos_of_lt (show start < stop from lt)
        exact .cons _ (stop.prev ne) _
          (ih _ Pos.prev_lt ⟨Pos.le_prev_iff_lt.mpr lt, fun cursor lo hi =>
            all cursor lo (Nat.lt_trans hi Pos.prev_lt)⟩)
          (_root_.String.Slice.Pattern.Model.CharPred.isLongestRevMatchAt_iff.mpr
            ⟨ne, rfl, all _ (Pos.le_prev_iff_lt.mpr lt) Pos.prev_lt⟩)

open _root_.String.Slice in
public theorem isLongestMatchAtChain_iff_toList :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.isLongestMatchAtChain_iff_toList := by
  intro p s a b
  apply isLongestMatchAtChain_iff.trans
  constructor
  · rintro ⟨le, all⟩
    refine ⟨le, fun c mem => ?_⟩
    obtain ⟨pos, ne, rfl⟩ := (Alternatives.String.Slice.mem_toList_copy_iff_exists_get).mp mem
    have upper := (Pos.ofSlice_lt_ofSlice_iff ..).mpr ((Pos.lt_endPos_iff _).mpr ne)
    rw [Pos.ofSlice_endPos] at upper
    rw [Pos.get_eq_get_ofSlice]
    exact all _ Pos.le_ofSlice upper
  · rintro ⟨le, all⟩
    refine ⟨le, fun cursor lo hi => ?_⟩
    let pos := Pos.slice cursor a b lo (Nat.le_of_lt hi)
    have ne : pos ≠ (s.slice a b le).endPos := by
      intro eq
      have same := congrArg Pos.ofSlice eq
      change Pos.ofSlice (Pos.slice cursor a b lo _) = _ at same
      rw [Pos.ofSlice_slice, Pos.ofSlice_endPos] at same
      exact Nat.ne_of_lt hi (congrArg (fun q : s.Pos => q.offset.byteIdx) same)
    exact all _ (Alternatives.String.Slice.mem_toList_copy_iff_exists_get.mpr ⟨pos, ne, Pos.get_slice⟩)

public theorem isLongestMatchAtChain_startPos_endPos_iff_toList :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.isLongestMatchAtChain_startPos_endPos_iff_toList := by
  intro p s
  apply isLongestMatchAtChain_iff_toList.trans
  have le : s.startPos ≤ s.endPos := _root_.String.Slice.Pos.le_endPos _
  have same := _root_.String.Slice.slice_eq_self_iff (s := s) (h := le) |>.mpr ⟨rfl, rfl⟩
  exact ⟨fun ⟨_, all⟩ c mem => all c (same.symm ▸ mem), fun all => ⟨le, fun c mem => all c (same ▸ mem)⟩⟩

public theorem isLongestRevMatchAtChain_startPos_endPos_iff_toList :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.isLongestRevMatchAtChain_startPos_endPos_iff_toList := by
  intro p s
  exact isLongestRevMatchAtChain_iff.trans (isLongestMatchAtChain_iff.symm.trans isLongestMatchAtChain_startPos_endPos_iff_toList)

private theorem selectPosition {α : Type} {condition : Prop} [Decidable condition]
    (next : ¬condition → α) (accepted : ¬condition → Bool) (pos : α) :
    (if h : condition then none else if accepted h then some (next h) else none) = some pos ↔
      ∃ h : ¬condition, pos = next h ∧ accepted h = true := by
  by_cases h : condition
  · rw [dite_eq_left h]
    exact ⟨(fun eq => nomatch eq), fun ⟨ne, _⟩ => (ne h).elim⟩
  · rw [dite_eq_right h]
    split
    next yes => exact ⟨fun eq => ⟨h, (Option.some.inj eq).symm, yes⟩, fun ⟨_, eq, _⟩ => congrArg some eq.symm⟩
    next no => exact ⟨(fun eq => nomatch eq), fun ⟨_, _, yes⟩ => (no yes).elim⟩

public theorem instLawfulForwardPatternModelForallCharBool :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.instLawfulForwardPatternModelForallCharBool := by
  intro p
  constructor
  intro s pos
  exact (selectPosition (s.startPos.next ·) (fun h => p (s.startPos.get h)) pos).trans
    _root_.String.Slice.Pattern.Model.CharPred.isLongestMatch_iff.symm

public theorem instLawfulBackwardPatternModelForallCharBool :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.instLawfulBackwardPatternModelForallCharBool := by
  intro p
  constructor
  intro s pos
  exact (selectPosition (s.endPos.prev ·)
    (fun h => p ((s.endPos.prev h).get _root_.String.Slice.Pos.prev_ne_endPos)) pos).trans
    _root_.String.Slice.Pattern.Model.CharPred.isLongestRevMatch_iff.symm

namespace Decidable

public theorem isValidSearchFrom_iff_isValidSearchFrom_decide :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.Decidable.isValidSearchFrom_iff_isValidSearchFrom_decide := by
  intro p inst s pos steps
  exact ⟨forwardSearch _root_.String.Slice.Pattern.Model.CharPred.Decidable.isLongestMatchAt_iff_isLongestMatchAt_decide,
    forwardSearch _root_.String.Slice.Pattern.Model.CharPred.Decidable.isLongestMatchAt_iff_isLongestMatchAt_decide.symm⟩

public theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_decide :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.Decidable.isValidRevSearchFrom_iff_isValidRevSearchFrom_decide := by
  intro p inst s pos steps
  exact ⟨reverseSearch _root_.String.Slice.Pattern.Model.CharPred.Decidable.isLongestRevMatchAt_iff_isLongestRevMatchAt_decide,
    reverseSearch _root_.String.Slice.Pattern.Model.CharPred.Decidable.isLongestRevMatchAt_iff_isLongestRevMatchAt_decide.symm⟩

public theorem instLawfulBackwardPatternModelForallCharProp :
    type_of% @_root_.String.Slice.Pattern.Model.CharPred.Decidable.instLawfulBackwardPatternModelForallCharProp := by
  intro p inst
  constructor
  intro s pos
  exact (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff
    (pat := fun c => decide (p c)) pos).trans
    _root_.String.Slice.Pattern.Model.CharPred.Decidable.isLongestRevMatch_iff_isLongestRevMatch_decide.symm

end Decidable
end CharPred

namespace Char

public theorem isValidSearchFrom_iff_isValidSearchFrom_beq :
    type_of% @_root_.String.Slice.Pattern.Model.Char.isValidSearchFrom_iff_isValidSearchFrom_beq := by
  intro c s pos steps
  exact ⟨forwardSearch _root_.String.Slice.Pattern.Model.Char.isLongestMatchAt_iff_isLongestMatchAt_beq,
    forwardSearch _root_.String.Slice.Pattern.Model.Char.isLongestMatchAt_iff_isLongestMatchAt_beq.symm⟩

public theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_beq :
    type_of% @_root_.String.Slice.Pattern.Model.Char.isValidRevSearchFrom_iff_isValidRevSearchFrom_beq := by
  intro c s pos steps
  exact ⟨reverseSearch _root_.String.Slice.Pattern.Model.Char.isLongestRevMatchAt_iff_isLongestRevMatchAt_beq,
    reverseSearch _root_.String.Slice.Pattern.Model.Char.isLongestRevMatchAt_iff_isLongestRevMatchAt_beq.symm⟩

public theorem instLawfulForwardPatternModelChar :
    type_of% @_root_.String.Slice.Pattern.Model.Char.instLawfulForwardPatternModelChar := by
  intro c
  constructor
  intro s pos
  exact (_root_.String.Slice.Pattern.Model.LawfulForwardPatternModel.skipPrefix?_eq_some_iff
    (pat := fun x => x == c) pos).trans
    _root_.String.Slice.Pattern.Model.Char.isLongestMatch_iff_isLongestMatch_beq.symm

public theorem instLawfulBackwardPatternModelChar :
    type_of% @_root_.String.Slice.Pattern.Model.Char.instLawfulBackwardPatternModelChar := by
  intro c
  constructor
  intro s pos
  exact (_root_.String.Slice.Pattern.Model.LawfulBackwardPatternModel.skipSuffix?_eq_some_iff
    (pat := fun x => x == c) pos).trans
    _root_.String.Slice.Pattern.Model.Char.isLongestRevMatch_iff_isLongestRevMatch_beq.symm

end Char

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

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

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem prefixFunction.go._proof_1 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_1) := by
  intro pat stack bound k miss atZero
  subst k
  exact miss ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_zero) bound)

public theorem prefixFunction.go._proof_3 :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_3) :=
  private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.go._proof_1

open _root_.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem prefixFunction.le_go_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff) := by
  intro pat stack bound k limit
  delta prefixFunction.go
  let P (n largest : Nat) := k ≤ largest ↔ ∃ i, k ≤ i ∧ i ≤ n ∧ PartialMatch pat pat i (stack + 1)
  apply (private_decl% OmegaChecks.InitPort.Alternatives.fixInvariant) (P := P)
  intro n cont ih
  dsimp only [P]
  by_cases hit : PartialMatch pat pat n (stack + 1)
  · rw [dite_eq_left hit]
    exact ⟨fun h => ⟨_, h, Nat.le_refl _, hit⟩, fun ⟨a, lo, hi, _⟩ => Nat.le_trans lo hi⟩
  · rw [dite_eq_right hit]
    cases n with
    | zero => exact (hit (partialMatch_zero bound)).elim
    | succ n =>
      have prev := ih n (Nat.lt_succ_self n)
      constructor
      · intro h
        obtain ⟨a, lo, hi, yes⟩ := prev.mp h
        exact ⟨a, lo, Nat.le_succ_of_le hi, yes⟩
      · rintro ⟨a, lo, hi, yes⟩
        refine prev.mpr ⟨a, lo, ?_, yes⟩
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi (fun eq => by
          subst a
          exact hit yes))

public theorem le_prefixFunction_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff) := by
  intro k pat stack bound
  exact (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff)

public theorem prefixFunction_le_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff) := by
  intro k pat stack bound
  constructor
  · intro le j hj hst hit
    exact Nat.not_lt_of_ge le (Nat.lt_of_lt_of_le hj ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hst, hit⟩))
  · intro maximal
    apply Nat.le_of_not_lt
    intro gt
    obtain ⟨j, lo, hi, hit⟩ := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mp (Nat.le_refl (prefixFunction pat stack bound))
    exact maximal _ (Nat.lt_of_lt_of_le gt lo) hi hit

public theorem prefixFunction_eq_iff :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff) := by
  intro k pat stack bound
  constructor
  · intro eq
    subst k
    have limit := Nat.le_refl (prefixFunction pat stack bound)
    have maximal := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mp limit
    obtain ⟨j, lo, hi, hit⟩ := (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mp limit
    obtain eq | lt := Nat.eq_or_lt_of_le lo
    · subst j
      exact ⟨hi, hit, maximal⟩
    · exact (maximal _ lt hi hit).elim
  · rintro ⟨hi, hit, maximal⟩
    exact Nat.le_antisymm ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mpr maximal) ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hi, hit⟩)

public theorem prefixFunctionRecurrence_eq_prefixFunction :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction) := by
  intro pat pos limit start hs
  delta prefixFunctionRecurrence prefixFunctionRecurrence._unary
  let best := prefixFunction pat pos limit
  let P (q : (g : Nat) ×' g < pos) (v : Nat) :=
    best ≤ q.1 + 1 → PartialMatch pat pat q.1 pos → v = best
  apply (private_decl% OmegaChecks.InitPort.Alternatives.fixInvariant) (P := P) (x := ⟨start, hs⟩)
  rintro ⟨g, hg⟩ cont ih upper hp
  dsimp only
  by_cases same : pat[g] = pat[pos]
  · rw [dite_eq_left same]
    exact Nat.le_antisymm ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨_, Nat.le_refl _, hg,
      partialMatch_add_one_add_one_iff.mpr ⟨hp, ⟨_, _, same⟩⟩⟩) upper
  · rw [dite_eq_right same]
    by_cases zero : g = 0
    · rw [dite_eq_left zero]
      subst g
      cases bestEq : best with
      | zero => rfl
      | succ n =>
        have nonzero : best = 1 := (Nat.le_antisymm upper (bestEq ▸ Nat.zero_lt_succ n))
        have hit := ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff).mp nonzero).2.1
        have byte := hit.getElem_eq 0 (Nat.zero_lt_succ 0)
        simp only [Nat.add_one_sub_one, Nat.add_zero] at byte
        exact (same byte).elim
    · rw [dite_eq_right zero]
      apply ih
      · apply (private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff).mpr
        intro k more small part
        have bound := ((private_decl% _root_.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff).mpr ⟨k, Nat.le_refl _, small, part⟩ :
          k ≤ prefixFunction pat pos limit)
        have kbound := Nat.le_trans bound upper
        cases k with
        | zero => exact (Nat.not_lt_zero _ more).elim
        | succ j =>
          obtain ⟨partialPrev, ⟨h₁, h₂, eq⟩⟩ := partialMatch_add_one_add_one_iff.mp part
          have jle : j ≤ g := Nat.le_of_succ_le_succ kbound
          have lt : j < g := Nat.lt_of_le_of_ne jle (fun h => by
            subst j
            exact same eq)
          have inner := hp.partialMatch_iff.mpr ⟨jle, partialPrev⟩
          exact Nat.not_lt_of_ge
            (inner.le_prefixFunction (Nat.pos_of_ne_zero zero) (Nat.le_pred_of_lt lt))
            (Nat.lt_of_succ_lt_succ more)
      · exact (hp.partialMatch_iff.mp (partialMatch_prefixFunction_sub_one (Nat.pos_of_ne_zero zero))).2

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher
open _root_.String _root_.String.Slice _root_.String.Slice.Pattern.Model _root_.String.Slice.Pattern.Model.ForwardSliceSearcher

public theorem Invariants.not_matchesAt_of_prefixFunction_eq :
    type_of% (private_decl% @_root_.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq) := by
  intro pat s stack needle h k hki hk pos lower upper hs hp different found
  have full := (matchesAt_iff_partialMatch h.isEmpty_eq_false).mp found
  change stack.byteIdx - needle.byteIdx ≤ pos.offset.byteIdx at lower
  change pos.offset.byteIdx < stack.byteIdx - k at upper
  by_cases inside : stack.byteIdx - pos.offset.byteIdx ≤ needle.byteIdx - 1
  · have truncated := full.partialMatch_of_le stack.byteIdx (by omega) (by omega)
    have inner := h.partialMatch.partialMatch_iff.mpr ⟨by omega, truncated⟩
    have bounded := inner.le_prefixFunction (by omega) (by omega)
    rw [hk] at bounded
    omega
  · have eq : stack = needle.offsetBy pos.offset := String.Pos.Raw.ext (by
      change stack.byteIdx = pos.offset.byteIdx + needle.byteIdx
      omega)
    subst stack
    have eqByte := full.getElem_eq needle.byteIdx (by simpa only [String.Pos.Raw.lt_iff,
      _root_.String.Slice.byteIdx_rawEndPos, _root_.String.Slice.utf8ByteSize_eq_size_toByteArray_copy] using hp)
    apply different
    simp only [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte]
    simpa only [Nat.add_sub_cancel, String.Pos.Raw.byteIdx_offsetBy, Nat.add_comm] using eqByte.symm

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model.ForwardSliceSearcher
