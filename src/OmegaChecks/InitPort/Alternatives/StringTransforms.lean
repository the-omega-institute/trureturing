module
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

/-! Character traversal, cursor membership, mapping and intercalation. -/

namespace OmegaChecks.InitPort.Alternatives

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
