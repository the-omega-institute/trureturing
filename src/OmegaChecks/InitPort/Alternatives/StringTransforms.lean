module
import all Init.Data.List.SplitOn.Lemmas
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Lemmas.Pattern.Split.Char
import all Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Consumers.Total
import all Init.Data.Iterators.Consumers.Collect
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Lemmas.Pattern.Split.Pred
import all Init.Data.String.Lemmas.Pattern.Split.Basic
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
import all Init.Data.String.Iterate
import all Init.Data.String.Lemmas.Iterate
import all Init.Data.String.Termination
import all Init.Data.String.Extra
import Init.Data.String.Lemmas.StringOrder
import Init.Data.List.BasicAux
import all Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import all Init.Data.String.Modify
import all Init.Data.String.Lemmas.Intercalate
import all Init.Data.String.Lemmas.Iter

/-! Character traversal, cursor membership, mapping and intercalation. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.Iter.joinString_eq : type_of% @_root_.Std.Iter.joinString_eq := by
  intro α β inst finite display it
  exact (_root_.Std.Iter.foldl_toList (it := it.map toString) (init := "")
    (f := fun a b : String => a ++ b)).symm.trans
    (congrArg _root_.String.join (_root_.Std.Iter.toList_map (it := it) (f := toString)))

public theorem Char.toLower._proof_1 : type_of% @_root_.Char.toLower._proof_1 := by
  intro c h
  left
  rw [UInt32.toNat_add, UInt32.toNat_sub_of_le _ _ (by decide : 'A'.val ≤ 'a'.val)]
  change (c.val.toNat + 32) % 2 ^ 32 < 55296
  have hi : c.val.toNat ≤ 90 := h.2
  have small := Nat.lt_of_le_of_lt (Nat.add_le_add_right hi 32) (show 122 < 55296 by decide)
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right hi 32) (show 122 < 2 ^ 32 by decide))]
  exact small

public theorem Char.toUpper._proof_1 : type_of% @_root_.Char.toUpper._proof_1 := by
  intro c h
  left
  have hi : c.val.toNat ≤ 122 := h.2
  have lo : 97 ≤ c.val.toNat := h.1
  have rebracket (x y z : UInt32) : x + (y - z) = (x + y) - z := by
    rw [UInt32.sub_eq_add_neg, UInt32.sub_eq_add_neg, UInt32.add_assoc]
  rw [rebracket]
  have addNat : (c.val + 'A'.val).toNat = c.val.toNat + 65 := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hi 65) (by decide : 187 < 2 ^ 32)
  have lower : 'a'.val ≤ c.val + 'A'.val := by
    change 97 ≤ (c.val + 'A'.val).toNat
    rw [addNat]
    exact Nat.le_trans lo (Nat.le_add_right ..)
  rw [UInt32.toNat_sub_of_le _ _ lower, addNat]
  exact Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_of_le_of_lt (Nat.add_le_add_right hi 65) (by decide))

public theorem String.mapAux._unary._proof_1 :
    type_of% (private_decl% @_root_.String.mapAux._unary._proof_1) := by
  intro f s p h
  change (p.pastModify f h).remainingBytes < p.remainingBytes
  rw [_root_.String.remainingBytes_pastModify]
  exact (_root_.String.Pos.lt_iff_remainingBytes_lt ..).mp (_root_.String.Pos.lt_next ..)

public theorem String.intercalate_append_of_ne_nil :
    type_of% @_root_.String.intercalate_append_of_ne_nil := by
  intro l m sep hl hm
  induction l with
  | nil => exact (hl rfl).elim
  | cons a tail ih =>
    cases tail with
    | nil =>
      exact (_root_.String.intercalate_cons_of_ne_nil hm).trans
        (congrArg (fun t => t ++ sep ++ sep.intercalate m) _root_.String.intercalate_singleton.symm)
    | cons b bs =>
      change sep.intercalate (a :: b :: (bs ++ m)) = _
      rw [List.cons_append] at ih
      rw [_root_.String.intercalate_cons_cons, ih (List.cons_ne_nil b bs),
        _root_.String.intercalate_cons_cons]
      repeat rw [String.append_assoc]

@[instance_reducible] public noncomputable def String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad :
    type_of% @_root_.String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad :=
  fun {_ _} {_} _ _ => finiteIteratorLoop

@[instance_reducible] public noncomputable def String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad :
    type_of% @_root_.String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad :=
  fun {_ _} {_} _ _ => finiteIteratorLoop

@[instance_reducible] public noncomputable def String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad :
    type_of% @_root_.String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad :=
  fun {_ _} _ _ => finiteIteratorLoop

@[instance_reducible] public noncomputable def String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad :
    type_of% @_root_.String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad :=
  fun {_ _} _ _ => finiteIteratorLoop

@[instance_reducible] public noncomputable def String.Slice.RevByteIterator.instForInCharOfMonad
    {m : Type u → Type v} [Monad m] : ForIn m String.Slice Char where
  forIn s b f :=
    @ForIn.forIn m _ Char (@Std.instForInIterOfMonadOfIteratorLoopId _ _ m _ _ finiteIteratorLoop)
      _ s.chars b f

-- The upstream character traversal unfolds to the corresponding string or slice instance.
public theorem String.Slice.forIn_eq_forIn_chars {β : Type u} {m : Type u → Type v} [Monad m]
    {s : _root_.String.Slice} {b : β} {f : Char → β → m (ForInStep β)} :
    forIn s b f = forIn s b f := rfl

public theorem String.forIn_eq_forIn_chars {β : Type u} {m : Type u → Type v} [Monad m]
    {s : _root_.String} {b : β} {f : Char → β → m (ForInStep β)} :
    forIn s b f = forIn s b f := rfl

public theorem String.Slice.Model.revPositionsFrom._proof_3 :
    type_of% (private_decl% @_root_.String.Slice.Model.revPositionsFrom._proof_3) := by
  intro s p h
  exact _root_.String.Slice.Pos.prev_lt (h := h)

public theorem String.Slice.Model.mem_positionsFrom : type_of% @_root_.String.Slice.Model.mem_positionsFrom := by
  intro s p q
  induction p using _root_.String.Slice.Pos.next_induction with
  | endPos =>
    rw [_root_.String.Slice.Model.positionsFrom_endPos]
    exact ⟨(fun h => nomatch h), fun h => (q.2 ((_root_.String.Slice.Pos.endPos_le _).mp h)).elim⟩
  | next p hp ih =>
    rw [_root_.String.Slice.Model.positionsFrom_eq_cons hp, List.mem_cons, ih, _root_.String.Slice.Pos.next_le_iff_lt]
    constructor
    · rintro (eq | lt)
      · cases eq
        exact Nat.le_refl _
      · exact Nat.le_of_lt lt
    · intro le
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · exact Or.inr lt
      · exact Or.inl (Subtype.ext (_root_.String.Slice.Pos.ext (String.Pos.Raw.ext eq.symm)))

public theorem String.Slice.Model.mem_positionsFrom_startPos :
    type_of% @_root_.String.Slice.Model.mem_positionsFrom_startPos := by
  intro s q
  exact String.Slice.Model.mem_positionsFrom.mpr (_root_.String.Slice.Pos.startPos_le _)

public theorem String.Model.revPositionsFrom._proof_3 :
    type_of% (private_decl% @_root_.String.Model.revPositionsFrom._proof_3) := by
  intro s p h
  exact _root_.String.Pos.prev_lt (h := h)

public theorem String.Model.mem_positionsFrom : type_of% @_root_.String.Model.mem_positionsFrom := by
  intro s p q
  induction p using _root_.String.Pos.next_induction with
  | endPos =>
    rw [_root_.String.Model.positionsFrom_endPos]
    exact ⟨(fun h => nomatch h), fun h => (q.2 ((_root_.String.Pos.endPos_le _).mp h)).elim⟩
  | next p hp ih =>
    rw [_root_.String.Model.positionsFrom_eq_cons hp, List.mem_cons, ih, _root_.String.Pos.next_le_iff_lt]
    constructor
    · rintro (eq | lt)
      · cases eq
        exact Nat.le_refl _
      · exact Nat.le_of_lt lt
    · intro le
      rcases Nat.lt_or_eq_of_le le with lt | eq
      · exact Or.inr lt
      · exact Or.inl (Subtype.ext (_root_.String.Pos.ext (String.Pos.Raw.ext eq.symm)))

public theorem String.Model.mem_positionsFrom_startPos :
    type_of% @_root_.String.Model.mem_positionsFrom_startPos := by
  intro s q
  exact String.Model.mem_positionsFrom.mpr (_root_.String.Pos.startPos_le _)

public theorem String.Model.map_get_positionsFrom_of_splits :
    type_of% @_root_.String.Model.map_get_positionsFrom_of_splits := by
  intro s p left right hp
  induction p using _root_.String.Pos.next_induction generalizing left right with
  | next p h ih =>
    obtain ⟨tail, rfl⟩ := hp.exists_eq_singleton_append h
    rw [_root_.String.Model.positionsFrom_eq_cons h, List.map_cons, String.toList_append,
      String.toList_singleton, List.singleton_append, ih hp.next]
  | endPos =>
    obtain ⟨_, rfl⟩ := (_root_.String.splits_endPos_iff.mp hp)
    rw [_root_.String.Model.positionsFrom_endPos]
    rfl

public theorem String.mem_toList_iff_exists_get : type_of% @_root_.String.mem_toList_iff_exists_get := by
  intro s c
  rw [← _root_.String.Model.map_get_positionsFrom_startPos]
  constructor
  · intro mem
    obtain ⟨pos, _, got⟩ := List.mem_map.mp mem
    exact ⟨pos.val, pos.property, got⟩
  · rintro ⟨pos, h, rfl⟩
    exact List.mem_map.mpr ⟨⟨pos, h⟩, String.Model.mem_positionsFrom_startPos, rfl⟩

public theorem String.le_antisymm : type_of% @_root_.String.le_antisymm := by
  intro a b le ge
  apply _root_.String.ext
  exact List.lex_trichotomous (r := (· < · : Char → Char → Prop))
    (fun _ _ ab ba => _root_.Char.le_antisymm (Nat.le_of_not_gt ba) (Nat.le_of_not_gt ab)) le ge

public theorem String.le_total : type_of% @_root_.String.le_total := by
  intro a b
  by_cases lt : b < a
  · exact Or.inr (_root_.String.lt_asymm lt)
  · exact Or.inl lt

public theorem String.le_trans : type_of% @_root_.String.le_trans := by
  intro a b c ab bc
  by_cases lt : a < b
  · exact fun ca => bc (_root_.String.lt_trans ca lt)
  · obtain rfl := String.le_antisymm ab lt
    exact bc

public theorem String.instLawfulOrderLT : type_of% @_root_.String.instLawfulOrderLT := by
  constructor
  intro a b
  exact ⟨fun h => ⟨_root_.String.lt_asymm h, fun notLT => notLT h⟩,
    fun h => Decidable.byContradiction h.2⟩

public noncomputable def String.removeLeadingSpaces (s : String) : String :=
  let newline := fun c : Char => c == '\n'
  let found := @_root_.String.Pos.find? _ (_root_.String.Slice.Pattern.ToForwardSearcher.DefaultForwardSearcher newline)
    inferInstance (fun _ => finiteIteratorLoop) s s.startPos newline inferInstance
  let width := match found.bind _root_.String.Pos.next? with
    | some pos => (private_decl% _root_.String.findLeadingSpacesSize.consumeSpaces) pos 0 s.utf8ByteSize
    | none => 0
  if width == 0 then s else (private_decl% _root_.String.removeNumLeadingSpaces) width s

public theorem String.Slice.toList_positionsFrom : type_of% @_root_.String.Slice.toList_positionsFrom := by
  intro s p
  induction p using _root_.String.Slice.Pos.next_induction with
  | endPos =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.String.Slice.Model.positionsFrom_endPos]
    dsimp only [_root_.Std.Iter.step, _root_.String.Slice.positionsFrom, _root_.Std.IterM.step,
      _root_.Std.Iterator.step, _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    rw [dite_eq_left (rfl : s.endPos = s.endPos)]
    rw [Id.run_pure, Std.Shrink.inflate_deflate]
    rfl
  | next p h ih =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.String.Slice.Model.positionsFrom_eq_cons h]
    dsimp only [_root_.Std.Iter.step, _root_.String.Slice.positionsFrom, _root_.Std.IterM.step,
      _root_.Std.Iterator.step, _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    rw [dite_eq_right h]
    rw [Id.run_pure, Std.Shrink.inflate_deflate]
    exact congrArg (List.cons _) ih

public theorem String.Slice.toList_revPositionsFrom : type_of% @_root_.String.Slice.toList_revPositionsFrom := by
  intro s p
  induction p using _root_.String.Slice.Pos.prev_induction with
  | startPos =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.String.Slice.Model.revPositionsFrom_startPos]
    dsimp only [_root_.Std.Iter.step, _root_.String.Slice.revPositionsFrom, _root_.Std.IterM.step,
      _root_.Std.Iterator.step, _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    rw [dite_eq_left (rfl : s.startPos = s.startPos)]
    rw [Id.run_pure, Std.Shrink.inflate_deflate]
    rfl
  | prev p h ih =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.String.Slice.Model.revPositionsFrom_eq_cons h]
    dsimp only [_root_.Std.Iter.step, _root_.String.Slice.revPositionsFrom, _root_.Std.IterM.step,
      _root_.Std.Iterator.step, _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
    rw [dite_eq_right h]
    rw [Id.run_pure, Std.Shrink.inflate_deflate]
    exact congrArg (List.cons _) ih

end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives.String.Slice
open _root_.String.Slice _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model

public theorem toList_splitToSubslice_of_isEmpty :
    type_of% @_root_.String.Slice.toList_splitToSubslice_of_isEmpty := by
  intro ρ pat model strict σ searcher iter finite lawful s empty
  have valid := @LawfulToForwardSearcherModel.isValidSearchFrom_toList ρ pat model σ searcher iter finite lawful s
  have terminal := _root_.String.Slice.startPos_eq_endPos_iff.mpr empty
  have noSteps {p : s.Pos} {steps : List (SearchStep s)}
      (hp : p = s.endPos) (valid : IsValidSearchFrom pat p steps) : steps = [] := by
    cases valid with
    | endPos => rfl
    | matched hit _ => exact (Pos.not_endPos_lt (hp ▸ hit.lt)).elim
    | mismatched lt _ _ => exact (Pos.not_endPos_lt (hp ▸ lt)).elim
  rw [private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps,
    noSteps terminal valid, terminal]
  rfl

end OmegaChecks.InitPort.Alternatives.String.Slice

namespace OmegaChecks.InitPort.Alternatives.String.Slice
open _root_.String.Slice _root_.String.Slice.Pattern _root_.String.Slice.Pattern.Model

private abbrev predSteps {s : String.Slice} (p : Char → Bool) (pos : s.Pos) :=
  (_root_.Std.Iter.mk (α := ToForwardSearcher.DefaultForwardSearcher p s) ⟨pos⟩).ensureTermination.toList

private theorem predSteps_end {s : String.Slice} {p : Char → Bool} :
    predSteps p s.endPos = [] := by
  unfold predSteps
  rw [_root_.Std.Iter.toList_ensureTermination_eq_match_step]
  dsimp only [_root_.Std.Iter.step, _root_.Std.IterM.step, _root_.Std.Iterator.step,
    _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
  rw [dite_eq_left rfl, Id.run_pure, Std.Shrink.inflate_deflate]
  rfl

private theorem predSteps_next {s : String.Slice} {p : Char → Bool} {pos : s.Pos} (h : pos ≠ s.endPos) :
    predSteps p pos = (if p (pos.get h) then .matched pos (pos.next h) else .rejected pos (pos.next h)) ::
      predSteps p (pos.next h) := by
  unfold predSteps
  rw [_root_.Std.Iter.toList_ensureTermination_eq_match_step]
  dsimp only [_root_.Std.Iter.step, _root_.Std.IterM.step, _root_.Std.Iterator.step,
    _root_.Std.Iter.toIterM, _root_.Std.IterM.internalState_mk]
  rw [dite_eq_right h]
  have getEq (hs : (s.sliceFrom pos).startPos ≠ (s.sliceFrom pos).endPos) :
      (s.sliceFrom pos).startPos.get hs = pos.get h := by
    rw [Pos.get_eq_get_ofSliceFrom]
    simp only [Pos.ofSliceFrom_startPos]
  split <;> rename_i stepEq
  · split at stepEq <;> rename_i outcome
    all_goals rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq
    all_goals cases stepEq
    all_goals dsimp only [ForwardPattern.skipPrefixOfNonempty?] at outcome
    all_goals rw [getEq] at outcome
    · split at outcome <;> rename_i accepted
      · cases outcome
        rw [ite_eq_left accepted, Pos.ofSliceFrom_next]
        simp only [Pos.ofSliceFrom_startPos]
        rfl
      · cases outcome
    · split at outcome <;> rename_i accepted
      · cases outcome
      · rw [ite_eq_right accepted]
        rfl
  · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq
  · split at stepEq <;> rw [Id.run_pure, Std.Shrink.inflate_deflate] at stepEq <;> cases stepEq

public theorem toList_splitToSubslice_bool :
    type_of% @_root_.String.Slice.toList_splitToSubslice_bool := by
  intro s p
  let splitAt (f pos : s.Pos) :=
    (private_decl% _root_.String.Slice.Pattern.Model.splitFromSteps) f (predSteps p pos)
  have splitList (f pos : s.Pos) (le : f ≤ pos) (a b : String) (hp : pos.Splits a b) :
      (splitAt f pos).map (String.Slice.copy ∘ String.Slice.Subslice.toSlice) =
      (b.toList.splitOnPPrepend p (s.subslice f pos le).copy.toList.reverse).map String.ofList := by
    induction pos using Pos.next_induction generalizing f a b with
    | endPos =>
      obtain rfl := hp.eq_right (s.splits_endPos)
      simp only [splitAt, predSteps_end, splitFromSteps, List.map_cons, Function.comp_apply, toSlice_subsliceFrom,
        List.map_nil, String.toList_empty, subslice_endPos, Subslice.copy_eq, List.splitOnPPrepend_nil,
        List.reverse_reverse, String.ofList_toList]
    | next pos h ih =>
      obtain ⟨rest, rfl⟩ := hp.exists_eq_singleton_append h
      have next := hp.next
      by_cases accepted : p (pos.get h) = true
      · unfold splitAt
        rw [predSteps_next h, ite_eq_left accepted]
        simp only [splitFromSteps, List.map_cons]
        rw [subslice!_eq_subslice le]
        have tail := ih (pos.next h) (Nat.le_refl _) _ _ next
        simp only [String.toList_append, String.toList_singleton, List.singleton_append,
          List.splitOnPPrepend_cons_pos (p := p) accepted, List.map_cons]
        simp only [Subslice.copy_eq, Function.comp_apply, toSlice_subslice, copy_slice_self, String.toList_empty,
          List.reverse_nil, List.splitOnPPrepend_nil_right, splitAt] at tail
        simp only [Function.comp_apply, toSlice_subslice, tail, Subslice.copy_eq, List.reverse_reverse,
          String.ofList_toList]
      · unfold splitAt
        rw [predSteps_next h, ite_eq_right accepted]
        simp only [splitFromSteps]
        have tail := ih f (Nat.le_trans le Pos.le_next) _ _ next
        simp only [String.toList_append, String.toList_singleton, List.singleton_append,
          List.splitOnPPrepend_cons_neg (p := p) (Bool.eq_false_iff.mpr accepted)]
        rw [show _ = _ from tail]
        have parts := (splits_slice (Nat.le_trans le Pos.le_next) (pos.slice f (pos.next h) le Pos.le_next)).eq_append
        simp only [Pos.ofSlice_slice, copy_slice_next, String.append_singleton] at parts
        simp only [Subslice.copy_eq, Function.comp_apply, toSlice_subslice, parts, String.toList_push, List.reverse_append, List.reverse_cons,
          List.reverse_nil, List.nil_append, List.cons_append]
  rw [private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps]
  have atStart := splitList s.startPos s.startPos (Nat.le_refl _) "" s.copy s.splits_startPos
  change List.map (copy ∘ Subslice.toSlice) (splitFromSteps s.startPos (predSteps p s.startPos)) = _ at atStart
  have steps : predSteps p s.startPos = (ToForwardSearcher.toSearcher p s).toList := by
    exact _root_.Std.Iter.toList_ensureTermination
  rw [steps] at atStart
  simpa only [Subslice.copy_eq, Function.comp_apply, toSlice_subslice, slice_startPos, copy_sliceTo_startPos,
    String.toList_empty, List.reverse_nil, List.splitOnPPrepend_nil_right] using atStart

public theorem toList_splitToSubslice_prop :
    type_of% @_root_.String.Slice.toList_splitToSubslice_prop := by
  intro s p _
  have same : (s.splitToSubslice p).toList = (s.splitToSubslice (fun c => decide (p c))).toList := by
    rw [private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps,
      private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps]
    rfl
  rw [same]
  exact _root_.String.Slice.toList_splitToSubslice_bool

public theorem toList_splitToSubslice_char :
    type_of% @_root_.String.Slice.toList_splitToSubslice_char := by
  intro s c
  have same : (s.splitToSubslice c).toList = (s.splitToSubslice (· == c)).toList := by
    rw [private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps,
      private_decl% _root_.String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps]
    rfl
  rw [same, List.splitOn_eq_splitOnP]
  exact _root_.String.Slice.toList_splitToSubslice_bool

end OmegaChecks.InitPort.Alternatives.String.Slice

namespace OmegaChecks.InitPort.Alternatives

public theorem List.splitOnP_eq_singleton :
    type_of% @_root_.List.splitOnP_eq_singleton := by
  intro α p xs misses
  have collect (ys acc : List α) (noSep : ∀ x ∈ ys, p x = false) :
      ys.splitOnPPrepend p acc = [acc.reverse ++ ys] := by
    induction ys generalizing acc with
    | nil => exact congrArg (fun l => [l]) (List.append_nil _).symm
    | cons a ys ih =>
      rw [List.splitOnPPrepend_cons_neg (noSep _ (.head _)),
        ih (a :: acc) (fun x mem => noSep x (.tail _ mem))]
      exact congrArg (fun l => [l]) ((congrArg (· ++ ys) (List.reverse_cons ..)).trans (List.append_assoc ..))
  exact collect xs [] misses

public theorem List.splitOnP_append_cons :
    type_of% @_root_.List.splitOnP_append_cons := by
  intro α p xs ys sep found
  have collect (zs acc : List α) :
      (zs ++ sep :: ys).splitOnPPrepend p acc = (zs.splitOnPPrepend p acc) ++ ys.splitOnP p := by
    induction zs generalizing acc with
    | nil => exact List.splitOnPPrepend_cons_pos found
    | cons a zs ih =>
      cases ha : p a with
      | false =>
        rw [List.cons_append, List.splitOnPPrepend_cons_neg ha, List.splitOnPPrepend_cons_neg ha]
        exact ih _
      | true =>
        rw [List.cons_append, List.splitOnPPrepend_cons_pos ha, List.splitOnPPrepend_cons_pos ha]
        exact congrArg (List.cons _) (ih [])
  exact collect xs []

public theorem List.splitOn_intercalate :
    type_of% @_root_.List.splitOn_intercalate := by
  intro α ls _ _ x absent nonempty
  induction ls with
  | nil => exact (nonempty rfl).elim
  | cons a rest ih =>
    have head := absent a (.head _)
    cases rest with
    | nil =>
      rw [List.intercalate_singleton]
      exact _root_.List.splitOn_eq_singleton head
    | cons b bs =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        List.splitOn_append_cons_self_of_not_mem head]
      exact congrArg (List.cons a) (ih (fun l mem => absent l (.tail _ mem)) (List.cons_ne_nil b bs))

end OmegaChecks.InitPort.Alternatives

namespace OmegaChecks.InitPort.Alternatives.String

private theorem ofListMapToList (l : List String) : (l.map String.toList).map String.ofList = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.map_cons, String.ofList_toList, ih]

public theorem toList_split_intercalate :
    type_of% @_root_.String.toList_split_intercalate := by
  intro c l absent
  rw [_root_.String.toList_split_char, _root_.String.toList_intercalate, String.toList_singleton]
  cases l with
  | nil =>
    rw [ite_eq_left (rfl : ([] : List String) = [])]
    simp only [List.map_nil, List.intercalate_nil, List.splitOn_eq_splitOnP, List.splitOnP_nil,
      List.map_cons, String.ofList_nil]
  | cons a as =>
    rw [ite_eq_right (List.cons_ne_nil a as), List.splitOn_intercalate c]
    · exact ofListMapToList _
    · intro chars mem
      obtain ⟨str, hs, rfl⟩ := List.mem_map.mp mem
      exact absent str hs
    · exact List.cons_ne_nil _ _

public theorem Slice.toList_split_intercalate :
    type_of% @_root_.String.Slice.toList_split_intercalate := by
  intro c l absent
  rw [_root_.String.Slice.intercalate_eq, String.copy_toSlice, OmegaChecks.InitPort.Alternatives.String.toList_split_intercalate]
  · cases l with
    | nil => rfl
    | cons a as => simp only [List.map_cons, ite_eq_right (List.cons_ne_nil a as), ite_eq_right (List.cons_ne_nil a.copy (as.map _))]
  · intro s mem
    obtain ⟨slice, hs, rfl⟩ := List.mem_map.mp mem
    exact absent slice hs

public theorem Slice.toList_split_intercalate_beq :
    type_of% @_root_.String.Slice.toList_split_intercalate_beq := by
  intro c l absent
  apply _root_.String.Slice.beq_list_iff.mpr
  rw [Slice.toList_split_intercalate absent]
  cases l with
  | nil =>
    rw [ite_eq_left (rfl : ([] : List String.Slice) = []), ite_eq_left (rfl : ([] : List String.Slice) = [])]
    exact congrArg (fun s => [s]) String.copy_toSlice.symm
  | cons a as => simp only [ite_eq_right (List.cons_ne_nil a as), List.map_cons]

public theorem toList_split_intercalate_beq :
    type_of% @_root_.String.toList_split_intercalate_beq := by
  intro c l absent
  apply _root_.String.Slice.beq_list_iff.mpr
  rw [toList_split_intercalate absent]
  cases l with
  | nil =>
    rw [ite_eq_left (rfl : ([] : List String) = []), ite_eq_left (rfl : ([] : List String) = [])]
    exact congrArg (fun s => [s]) String.copy_toSlice.symm
  | cons a as =>
    simp only [ite_eq_right (List.cons_ne_nil a as)]
    have same (xs : List String) : (xs.map String.toSlice).map String.Slice.copy = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => rw [List.map_cons, List.map_cons, String.copy_toSlice, ih]
    exact (same _).symm

end OmegaChecks.InitPort.Alternatives.String

namespace OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model

public theorem split_bool_eq_internal._proof_3 :
    type_of% @_root_.String.Slice.Pattern.Model.split_bool_eq_internal._proof_3 := by
  intro s f curr hle h
  exact Nat.le_trans hle _root_.String.Slice.Pos.le_next

end OmegaChecks.InitPort.Alternatives.String.Slice.Pattern.Model
