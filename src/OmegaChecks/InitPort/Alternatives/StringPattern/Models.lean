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

/-! Byte comparisons and pattern models for slices and characters. -/

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
