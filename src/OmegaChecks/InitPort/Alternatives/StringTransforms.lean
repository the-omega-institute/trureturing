module
import all OmegaChecks.InitPort.Alternatives.FiniteLoop
import all Init.Data.String.Iterate
import all Init.Data.Char.Basic
import Init.Data.UInt.Lemmas
import all Init.Data.String.Modify
import all Init.Data.String.Lemmas.Intercalate

/-! Termination of character mapping and intercalation of nonempty lists. -/

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

end OmegaChecks.InitPort.Alternatives
