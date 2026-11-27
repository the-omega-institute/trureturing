module
import Init.LawfulBEqTactics
public import Init.Data.String.Pattern.String
public import Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.ByteArray.Lemmas
import all Init.Data.Char.Ordinal
import all Init.Data.Iterators.Consumers.Access
import all Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.List.BasicAux
import all Init.Data.List.Control
import all Init.Data.List.Count
import all Init.Data.List.Erase
import all Init.Data.List.Impl
import all Init.Data.List.Lemmas
import all Init.Data.List.Lex
import all Init.Data.List.MapIdx
import all Init.Data.List.Nat.Basic
import all Init.Data.List.Nat.Modify
import all Init.Data.List.Range
import all Init.Data.List.Sort.Lemmas
import all Init.Data.List.Sublist
import all Init.Data.Nat.Lemmas
import all Init.Data.String.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Pattern.String
import all Init.Data.Nat.Gcd
import all Init.WFComputable
import all Init.Data.List.Sort.Impl
import all Init.Data.BitVec.Lemmas
import all Init.Data.Array.Basic
import all Init.Data.Array.Attach
import all Init.Data.Vector.Attach
import all Init.Data.List.ToArray
import all Init.Data.List.SplitOn.Basic
namespace OmegaChecks.InitPort.Alternatives

/-- A course-of-values induction step can reuse the theorem on its original arguments. -/
local macro "induction_step% " parent:term : term =>
  `(by intros; apply $parent <;> assumption)

public theorem Nat.pow_eq_zero._f : type_of% @_root_.Nat.pow_eq_zero._f :=
  induction_step% @_root_.Nat.pow_eq_zero

public theorem Nat.mul_add_div._f : type_of% @_root_.Nat.mul_add_div._f :=
  induction_step% @_root_.Nat.mul_add_div

public theorem List.append_cancel_right._f : type_of% @_root_.List.append_cancel_right._f :=
  induction_step% @_root_.List.append_cancel_right

public theorem List.mem_replicate._f : type_of% @_root_.List.mem_replicate._f :=
  induction_step% @_root_.List.mem_replicate

public theorem List.mem_map._f : type_of% @_root_.List.mem_map._f :=
  induction_step% @_root_.List.mem_map

public theorem List.isSublist_iff_sublist._f : type_of% @_root_.List.isSublist_iff_sublist._f :=
  induction_step% @_root_.List.isSublist_iff_sublist

public theorem List.count_erase._f : type_of% @_root_.List.count_erase._f :=
  induction_step% @_root_.List.count_erase

public theorem List.mem_range'._f : type_of% @_root_.List.mem_range'._f :=
  induction_step% @_root_.List.mem_range'

public theorem List.erase_eq_eraseP._f : type_of% @_root_.List.erase_eq_eraseP._f :=
  induction_step% @_root_.List.erase_eq_eraseP

public theorem List.eraseIdx_eq_self._f : type_of% @_root_.List.eraseIdx_eq_self._f :=
  induction_step% @_root_.List.eraseIdx_eq_self

public theorem List.getElem?_modify._f : type_of% @_root_.List.getElem?_modify._f :=
  induction_step% @_root_.List.getElem?_modify

public theorem List.mem_eraseIdx_iff_getElem._f : type_of% @_root_.List.mem_eraseIdx_iff_getElem._f :=
  induction_step% @_root_.List.mem_eraseIdx_iff_getElem

public theorem List.getElem?_mapIdx_go._f : type_of% @_root_.List.getElem?_mapIdx_go._f :=
  induction_step% @_root_.List.getElem?_mapIdx_go

public theorem List.map_lt._f : type_of% @_root_.List.map_lt._f :=
  induction_step% @_root_.List.map_lt

public theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract._unary :
    type_of% (private_decl% @_root_.ByteArray.utf8Decode?go_eq_utf8Decode?go_extract._unary) :=
  fun _ => _root_.ByteArray.utf8Decode?go_eq_utf8Decode?go_extract

public theorem Std.Iter.atIdxSlow?.induct_unfolding._unary :
    type_of% @_root_.Std.Iter.atIdxSlow?.induct_unfolding._unary :=
  fun motive yieldZero yieldSucc skip done x =>
    _root_.Std.Iter.atIdxSlow?.induct_unfolding motive yieldZero yieldSucc skip done x.1 x.2

public theorem List.length_merge._unary : type_of% @_root_.List.length_merge._unary :=
  fun s p => _root_.List.length_merge s p.1 p.2

public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq._proof_1_10 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq._proof_1_10) :=
  fun h denied => denied h

public theorem ByteArray.utf8DecodeChar?.le_val_assemble₄._proof_1_4 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.le_val_assemble₄._proof_1_4) :=
  fun h denied => denied h

public theorem Char.succ?_eq._proof_1_6 :
    type_of% (private_decl% @_root_.Char.succ?_eq._proof_1_6) :=
  fun h denied => denied (Nat.lt_succ_of_lt h)

public theorem DerivingHelpers.and_true_curry : type_of% @_root_.DerivingHelpers.and_true_curry := by
  intro a b P f
  cases a <;> cases b <;> exact fun h => by first | exact f rfl rfl | nomatch h

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_16 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_16) := by
  intro pat i hi
  cases i with
  | zero => exact Nat.le_refl 0
  | succ i => exact False.elim (Nat.not_succ_le_zero i (Nat.le_of_succ_le_succ hi))

public theorem ByteArray.extract_eq_empty_iff._proof_1_1 :
    type_of% (private_decl% @ByteArray.extract_eq_empty_iff._proof_1_1) :=
  fun h => h Nat.sub_eq_zero_iff_le

public theorem Std.Iterators.Types.Take.PlausibleStep._proof_1 :
    type_of% (private_decl% @Std.Iterators.Types.Take.PlausibleStep._proof_1) := by
  intro α m β inst it ne pos denied
  exact denied (Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne pos ne.symm))

public theorem String.Pos.isValidUTF8_extract._proof_1_1 :
    type_of% (private_decl% @String.Pos.isValidUTF8_extract._proof_1_1) := by
  intro _ a b h₁ h₂
  exact (Nat.le_total a.offset.byteIdx b.offset.byteIdx).elim h₁ h₂

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_1 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_1) :=
  fun _ _ positive denied => denied (Nat.sub_one_lt_of_lt positive)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance._proof_1 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance._proof_1) :=
  fun _ _ _ h denied => denied (Nat.lt_of_le_of_lt (Nat.sub_le ..) h)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_7 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_7) :=
  fun _ _ bound _ h denied => denied (Nat.lt_of_lt_of_le h bound)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_5 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_5) :=
  fun _ _ h notLt notEq => notEq (Nat.le_antisymm h (Nat.le_of_not_lt notLt))

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_8 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_8) :=
  fun _ _ _ h denied => denied h

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_12 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_12) :=
  fun _ ne denied => denied (Nat.pos_of_ne_zero ne)

public theorem String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_4 :
    type_of% (private_decl% @String.Slice.Pattern.ForwardSliceSearcher.buildTable._proof_4) :=
  fun _ _ _ _ _ _ _ _ ne h denied => denied (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) ne)


private theorem shifted_lt {x width : Nat} (shift : Nat) (h : x < 2 ^ width) :
    x * 2 ^ shift < 2 ^ (width + shift) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)

private theorem packed_lt {x y high low : Nat} (hx : x < 2 ^ high) (hy : y < 2 ^ low) :
    2 ^ low * x + y < 2 ^ (low + high) := calc
  _ < 2 ^ low * x + 2 ^ low := Nat.add_lt_add_left hy _
  _ = 2 ^ low * (x + 1) := (Nat.mul_succ ..).symm
  _ ≤ 2 ^ low * 2 ^ high := Nat.mul_le_mul_left _ hx
  _ = _ := (Nat.pow_add ..).symm

public theorem ByteArray.utf8DecodeChar?.assemble₃._proof_3 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₃._proof_3) := by
  intro _ _ _ h denied
  exact denied (Nat.lt_of_lt_of_le (shifted_lt (width := 4) 12 h) (by decide : 2 ^ 16 ≤ 2 ^ 32))

public theorem ByteArray.utf8DecodeChar?.assemble₃._proof_4 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₃._proof_4) := by
  intro _ _ _ h denied
  exact denied (Nat.lt_of_lt_of_le (shifted_lt (width := 6) 6 h) (by decide : 2 ^ 12 ≤ 2 ^ 32))

public theorem ByteArray.utf8DecodeChar?.assemble₃._proof_5 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₃._proof_5) := by
  intro _ _ _ hx hy denied
  exact denied (packed_lt (high := 6) (low := 6) hx hy)

public theorem ByteArray.utf8DecodeChar?.assemble₃._proof_6 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₃._proof_6) := by
  intro _ _ _ hw hx hy denied
  have low := packed_lt (high := 6) (low := 6) hx hy
  exact denied (Nat.lt_trans (packed_lt (high := 4) (low := 12) hw low)
    (by decide : 2 ^ 16 < 1114112))

public theorem ByteArray.utf8DecodeChar?.assemble₄._proof_3 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₄._proof_3) := by
  intro _ _ _ _ lo _ denied
  exact denied (Nat.lt_of_lt_of_le (by decide : 57343 < 65536) lo)

public theorem ByteArray.utf8DecodeChar?.assemble₄._proof_4 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₄._proof_4) := by
  intro _ _ _ _ _ hi denied
  exact denied (Nat.lt_of_le_of_lt hi (by decide : 1114111 < 1114112))


public theorem ByteArray.utf8DecodeChar?.assemble₄._proof_5 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₄._proof_5) := by
  intro w x y z hlo hhi
  let r := _root_.ByteArray.utf8DecodeChar?.assemble₄Unchecked w x y z
  have lo : 65536 ≤ r.toNat := Nat.le_of_not_lt fun h =>
    hlo ((UInt32.lt_ofNat_iff (by decide : 65536 < 2 ^ 32)).2 h)
  have hi : r.toNat ≤ 1114111 := Nat.le_of_not_lt fun h =>
    hhi ((UInt32.ofNat_lt_iff (by decide : 1114111 < 2 ^ 32)).2 h)
  exact .inr ⟨Nat.lt_of_lt_of_le (by decide : 57343 < 65536) lo,
    Nat.lt_of_le_of_lt hi (by decide : 1114111 < 1114112)⟩


private theorem shifted_byte_lt (b : UInt8) (n : Nat) (hn : n < 32) :
    (b.toUInt32 <<< UInt32.ofNat n).toNat < 2 ^ (8 + n) := by
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hn (by decide : 32 < 2 ^ 32)),
    Nat.mod_eq_of_lt hn, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  exact Nat.lt_of_le_of_lt (Nat.mod_le ..) (shifted_lt (width := 8) n b.toNat_lt_size)

public theorem ByteArray.utf8DecodeChar?.assemble₃._proof_7 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₃._proof_7) := by
  intro w x y notSurrogate
  let r := _root_.ByteArray.utf8DecodeChar?.assemble₃Unchecked w x y
  by_cases lo : r.toNat < 55296
  · exact Or.inl lo
  · have gt : 57343 < r.toNat := Nat.lt_of_not_ge fun hi =>
      notSurrogate ⟨(UInt32.ofNat_le_iff (by decide : 55296 < 2 ^ 32)).2 (Nat.le_of_not_lt lo),
        (UInt32.le_ofNat_iff (by decide : 57343 < 2 ^ 32)).2 hi⟩
    refine Or.inr ⟨gt, Nat.lt_trans ?_ (by decide : 2 ^ 20 < 1114112)⟩
    show r.toNat < 2 ^ 20
    rw [show r = _root_.ByteArray.utf8DecodeChar?.assemble₃Unchecked w x y from rfl,
      _root_.ByteArray.utf8DecodeChar?.assemble₃Unchecked, UInt32.toNat_or, UInt32.toNat_or,
      UInt8.toNat_toUInt32]
    apply Nat.or_lt_two_pow
    · apply Nat.or_lt_two_pow
      · exact shifted_byte_lt (w &&& 15) 12 (by decide)
      · exact Nat.lt_of_lt_of_le (shifted_byte_lt (x &&& 63) 6 (by decide))
          (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 14 ≤ 20))
    · exact Nat.lt_of_lt_of_le (UInt8.toNat_lt_size (y &&& 63))
        (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 8 ≤ 20))


public theorem ByteArray.utf8DecodeChar?.assemble₁._proof_3 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₁._proof_3) := by
  intro w _
  rw [UInt8.toNat_toUInt32]
  exact Or.inl (Nat.lt_trans w.toNat_lt_size (by decide : 2 ^ 8 < 55296))

public theorem ByteArray.utf8DecodeChar?.assemble₂._proof_3 :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.assemble₂._proof_3) := by
  intro w x
  refine Or.inl (Nat.lt_trans ?_ (by decide : 2 ^ 14 < 55296))
  rw [_root_.ByteArray.utf8DecodeChar?.assemble₂Unchecked, UInt32.toNat_or, UInt8.toNat_toUInt32]
  exact Nat.or_lt_two_pow (shifted_byte_lt (w &&& 31) 6 (by decide))
    (Nat.lt_of_lt_of_le (UInt8.toNat_lt_size (x &&& 63))
      (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 8 ≤ 14)))

public theorem List.findRev?TR.eq_1 :
    type_of% (private_decl% @_root_.List.findRev?TR.eq_1) := by
  intros
  rw [← _root_.List.findRev?_eq_findRev?TR]
  exact _root_.List.findRev?_eq_find?_reverse

public theorem List.findSomeRev?TR.eq_1 :
    type_of% (private_decl% @_root_.List.findSomeRev?TR.eq_1) := by
  intros
  rw [← _root_.List.findSomeRev?_eq_findSomeRev?TR]
  exact _root_.List.findSomeRev?_eq_findSome?_reverse

public theorem List.foldrTR.eq_1 :
    type_of% (private_decl% @_root_.List.foldrTR.eq_1) := by
  intro α β f b xs
  rw [← _root_.List.foldr_eq_foldrTR]
  exact _root_.Array.foldr_toList (xs := xs.toArray) f

public theorem List.setTR.eq_1 :
    type_of% (private_decl% @_root_.List.setTR.eq_1) := by
  intro α xs i a
  rw [← _root_.List.set_eq_setTR]
  exact ((private_decl% @_root_.List.set_eq_setTR.go) α xs a #[] xs i rfl).symm

public theorem List.erasePTR.eq_1 :
    type_of% (private_decl% @_root_.List.erasePTR.eq_1) := by
  intro α p xs
  rw [← _root_.List.eraseP_eq_erasePTR]
  exact ((private_decl% @_root_.List.eraseP_eq_erasePTR.go) α p xs #[] xs rfl).symm

public theorem List.modifyTR.eq_1 :
    type_of% (private_decl% @_root_.List.modifyTR.eq_1) := by
  intro α xs i f
  rw [← _root_.List.modify_eq_modifyTR]
  exact ((private_decl% @_root_.List.modifyTR_go_eq) (f := f) (acc := #[]) xs i).symm

public theorem List.insertIdxTR.eq_1 :
    type_of% (private_decl% @_root_.List.insertIdxTR.eq_1) := by
  intro α xs i a
  rw [← _root_.List.insertIdx_eq_insertIdxTR]
  exact ((private_decl% @_root_.List.insertIdxTR_go_eq) (a := a) (acc := #[]) i xs).symm

public theorem List.zipIdxTR.eq_1 :
    type_of% (private_decl% @_root_.List.zipIdxTR.eq_1) := by
  intro α xs n
  rw [← _root_.List.zipIdx_eq_zipIdxTR, ← _root_.Array.foldr_toList]
  exact congrArg Prod.snd ((private_decl% @_root_.List.zipIdx_eq_zipIdxTR.go) α xs n).symm

public theorem List.intercalateTR.eq_2 :
    type_of% (private_decl% @_root_.List.intercalateTR.eq_2) := by
  intro α sep xs
  rw [← _root_.List.intercalate_eq_intercalateTR]
  exact _root_.List.intercalate_singleton

private theorem pushTail (acc : Array α) (x : α) (xs : List α) :
    (acc.push x).toList ++ xs = acc.toList ++ x :: xs := by
  rw [Array.toList_push, List.append_assoc]
  rfl

private theorem takeAcc (all : List α) (xs : List α) (n : Nat) (acc : Array α)
    (parts : all = acc.toList ++ xs) :
    List.takeTR.go all xs n acc = acc.toList ++ xs.take n := by
  induction xs generalizing n acc with
  | nil => cases n <;> exact parts
  | cons x xs ih =>
    cases n with
    | zero => exact (List.append_nil _).symm
    | succ n =>
      exact (ih n (acc.push x) (parts.trans (pushTail _ _ _).symm)).trans (pushTail _ _ _)

public theorem List.takeTR.eq_1 :
    type_of% (private_decl% @_root_.List.takeTR.eq_1) := by
  intro α n xs
  rw [← _root_.List.take_eq_takeTR]
  exact (takeAcc xs xs n #[] rfl).symm

private theorem eraseIdxAcc (all : List α) (xs : List α) (n : Nat) (acc : Array α)
    (parts : all = acc.toList ++ xs) :
    List.eraseIdxTR.go all xs n acc = acc.toList ++ xs.eraseIdx n := by
  induction xs generalizing n acc with
  | nil => cases n <;> exact parts
  | cons x xs ih =>
    cases n with
    | zero => exact Array.toListAppend_eq
    | succ n =>
      exact (ih n (acc.push x) (parts.trans (pushTail _ _ _).symm)).trans (pushTail _ _ _)

public theorem List.eraseIdxTR.eq_1 :
    type_of% (private_decl% @_root_.List.eraseIdxTR.eq_1) := by
  intro α xs n
  rw [← _root_.List.eraseIdx_eq_eraseIdxTR]
  exact (eraseIdxAcc xs xs n #[] rfl).symm

private theorem takeWhileAcc (p : α → Bool) (all xs : List α) (acc : Array α)
    (parts : all = acc.toList ++ xs) :
    List.takeWhileTR.go p all xs acc = acc.toList ++ xs.takeWhile p := by
  induction xs generalizing acc with
  | nil => exact parts
  | cons x xs ih =>
    cases q : p x with
    | false =>
      simp only [List.takeWhileTR.go, List.takeWhile, q, Bool.cond_false]
      exact (List.append_nil _).symm
    | true =>
      simp only [List.takeWhileTR.go, List.takeWhile, q, Bool.cond_true]
      exact (ih (acc.push x) (parts.trans (pushTail _ _ _).symm)).trans (pushTail _ _ _)

public theorem List.takeWhileTR.eq_1 :
    type_of% (private_decl% @_root_.List.takeWhileTR.eq_1) := by
  intro α p xs
  rw [← _root_.List.takeWhile_eq_takeWhileTR]
  exact (takeWhileAcc p xs xs #[] rfl).symm

private theorem replaceAcc [BEq α] (all : List α) (old new : α) (xs : List α) (acc : Array α)
    (parts : all = acc.toList ++ xs) :
    List.replaceTR.go all old new xs acc = acc.toList ++ xs.replace old new := by
  induction xs generalizing acc with
  | nil => exact parts
  | cons x xs ih =>
    cases q : old == x with
    | false =>
      simp only [List.replaceTR.go, List.replace, q, Bool.cond_false]
      exact (ih (acc.push x) (parts.trans (pushTail _ _ _).symm)).trans (pushTail _ _ _)
    | true =>
      simp only [List.replaceTR.go, List.replace, q, Bool.cond_true]
      exact Array.toListAppend_eq

public theorem List.replaceTR.eq_1 :
    type_of% (private_decl% @_root_.List.replaceTR.eq_1) := by
  intro α inst xs old new
  rw [← _root_.List.replace_eq_replaceTR]
  exact (replaceAcc xs old new xs #[] rfl).symm

private theorem eraseAcc [BEq α] (all : List α) (a : α) (xs : List α) (acc : Array α)
    (parts : all = acc.toList ++ xs) :
    List.eraseTR.go all a xs acc = acc.toList ++ xs.erase a := by
  induction xs generalizing acc with
  | nil => exact parts
  | cons x xs ih =>
    cases q : x == a with
    | false =>
      simp only [List.eraseTR.go, List.erase, q, Bool.cond_false]
      exact (ih (acc.push x) (parts.trans (pushTail _ _ _).symm)).trans (pushTail _ _ _)
    | true =>
      simp only [List.eraseTR.go, List.erase, q, Bool.cond_true]
      exact Array.toListAppend_eq

public theorem List.eraseTR.eq_1 :
    type_of% (private_decl% @_root_.List.eraseTR.eq_1) := by
  intro α inst xs a
  rw [← _root_.List.erase_eq_eraseTR]
  exact (eraseAcc xs a xs #[] rfl).symm

public theorem List.intercalateTR.eq_3 :
    type_of% (private_decl% @_root_.List.intercalateTR.eq_3) := by
  intro α sep x xs _
  rw [← _root_.List.intercalate_eq_intercalateTR]
  exact ((private_decl% @_root_.List.intercalate_eq_intercalateTR.go) α sep (acc := #[]) (x := x) xs).symm

public theorem Nat.gcd.eq_def : type_of% (private_decl% @_root_.Nat.gcd.eq_def) := by
  intro m n
  by_cases h : m = 0
  · subst m
    rw [ite_eq_left rfl, Nat.gcd_zero_left]
  · rw [ite_eq_right h, Nat.gcd_rec]

public theorem Acc.recC.eq_def.{v, u} : type_of% (private_decl% @_root_.Acc.recC.eq_def.{v, u}) := by
  intro α r motive step a t
  rw [← _root_.Acc.rec_eq_recC]
  cases t
  rfl

public theorem List.MergeSort.Internal.mergeTR.eq_1 :
    type_of% (private_decl% @_root_.List.MergeSort.Internal.mergeTR.eq_1) := by
  intro α left right le
  rw [← _root_.List.MergeSort.Internal.merge_eq_mergeTR]
  exact (private_decl% @_root_.List.MergeSort.Internal.mergeTR_go_eq (le := le) (l₁ := left) (l₂ := right) (acc := [])).symm

public theorem List.MergeSort.Internal.mergeSortTR.eq_1 :
    type_of% (private_decl% @_root_.List.MergeSort.Internal.mergeSortTR.eq_1) := by
  intro α xs le
  rw [← _root_.List.MergeSort.Internal.mergeSort_eq_mergeSortTR]
  exact ((private_decl% @_root_.List.MergeSort.Internal.mergeSortTR_run_eq_mergeSort) (le := le) ⟨xs, rfl⟩).symm

public theorem List.MergeSort.Internal.mergeSortTR₂.eq_1 :
    type_of% (private_decl% @_root_.List.MergeSort.Internal.mergeSortTR₂.eq_1) := by
  intro α xs le
  rw [← _root_.List.MergeSort.Internal.mergeSort_eq_mergeSortTR₂]
  exact ((private_decl% @_root_.List.MergeSort.Internal.mergeSortTR₂_run_eq_mergeSort) (le := le) ⟨xs, rfl⟩).symm

public theorem BitVec.flattenListFast.eq_1 :
    type_of% (private_decl% @_root_.BitVec.flattenListFast.eq_1) := by
  intro n xs
  rw [← _root_.BitVec.flattenList_eq_flattenListFast, _root_.BitVec.flattenList.toNatAux_eq,
    _root_.BitVec.ofNat_toNat, _root_.BitVec.setWidth_eq]

public theorem Array.pmapImpl.eq_1 :
    type_of% (private_decl% @_root_.Array.pmapImpl.eq_1) := by
  intro α β P f xs H
  rw [← _root_.Array.pmap_eq_pmapImpl, _root_.Array.map_attachWith_eq_pmap]
  apply _root_.Array.pmap_congr_left
  intros
  rfl

public theorem Vector.pmapImpl.eq_1 :
    type_of% (private_decl% @_root_.Vector.pmapImpl.eq_1) := by
  intro α β n P f xs H
  rw [← _root_.Vector.pmap_eq_pmapImpl, _root_.Vector.map_attachWith_eq_pmap]
  apply _root_.Vector.pmap_congr_left
  intros
  rfl


public theorem Array.eraseIdxIfInBounds.eq_1 :
    type_of% (private_decl% @_root_.Array.eraseIdxIfInBounds.eq_1) := by
  intro α xs i
  obtain ⟨xs⟩ := xs
  change xs.toArray.eraseIdxIfInBounds i = if h : i < xs.toArray.size then xs.toArray.eraseIdx i h else xs.toArray
  split
  next h => rw [_root_.List.eraseIdxIfInBounds_toArray, _root_.List.eraseIdx_toArray]
  next h => rw [_root_.List.eraseIdxIfInBounds_toArray,
      _root_.List.eraseIdx_of_length_le (Nat.le_of_not_lt h)]

private theorem splitAcc (p : α → Bool) (xs : List α) (acc : Array α) (out : Array (List α)) :
    List.splitOnPTR.go p xs acc out = out.toList ++ List.splitOnPPrepend p xs acc.toList.reverse := by
  induction xs generalizing acc out with
  | nil =>
    rw [List.splitOnPTR.go, Array.toListAppend_eq, List.splitOnPPrepend, List.reverse_reverse]
  | cons x xs ih =>
    by_cases hit : p x
    · rw [List.splitOnPTR.go, ite_eq_left hit, List.splitOnPPrepend, ite_eq_left hit, ih,
        Array.toList_push, List.append_assoc, List.reverse_reverse]
      rfl
    · rw [List.splitOnPTR.go, ite_eq_right hit, List.splitOnPPrepend, ite_eq_right hit, ih,
        Array.toList_push, List.reverse_append]
      rfl

public theorem List.splitOnPTR.eq_1 :
    type_of% (private_decl% @_root_.List.splitOnPTR.eq_1) := by
  intro α p xs
  rw [← _root_.List.splitOnP_eq_splitOnPTR]
  exact (splitAcc p xs #[] #[]).symm

public theorem String.Slice.Pos.nextFast.eq_1 :
    type_of% (private_decl% @_root_.String.Slice.Pos.nextFast.eq_1) := by
  intro s pos h
  rw [← _root_.String.Slice.Pos.next_eq_nextFast]
  simp [_root_.String.Slice.Pos.ext_iff, _root_.String.Pos.Raw.ext_iff, _root_.String.Slice.Pos.get_eq_get_str]
  omega


private theorem neighbors (xs : List α) (i : Nat) (hi : i < xs.length) (later : i + 1 < xs.length) :
    xs.eraseIdx i = ((xs.set (i+1) xs[i]).set i xs[i+1]).eraseIdx (i+1) := by
  induction i generalizing xs with
  | zero =>
    match xs with
    | [] => exact False.elim (Nat.not_lt_zero _ hi)
    | [_] => exact False.elim ((Nat.lt_irrefl 1) later)
    | _ :: _ :: _ => rfl
  | succ i ih =>
    match xs with
    | [] => exact False.elim (Nat.not_lt_zero _ hi)
    | x :: ys => exact congrArg (List.cons x) (ih ys (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ later))

private theorem lastErase (xs : List α) (i : Nat) (hi : i < xs.length) (last : ¬ i + 1 < xs.length) :
    xs.eraseIdx i = xs.dropLast := by
  induction i generalizing xs with
  | zero =>
    match xs with
    | [] => exact False.elim (Nat.not_lt_zero _ hi)
    | [_] => rfl
    | a :: b :: ys => exact False.elim (last (Nat.succ_lt_succ (Nat.zero_lt_succ _)))
  | succ i ih =>
    match xs with
    | [] => exact False.elim (Nat.not_lt_zero _ hi)
    | [x] => exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hi))
    | x :: y :: ys =>
      exact congrArg (List.cons x) (ih (y :: ys) (Nat.lt_of_succ_lt_succ hi) (fun h => last (Nat.succ_lt_succ h)))

private theorem nativeSwap (xs : List α) (i j : Nat) (hi : i < xs.toArray.size) (hj : j < xs.toArray.size) :
    xs.toArray.swap i j hi hj = ((xs.set i xs[j]).set j xs[i]).toArray := by rfl

private theorem nativePop (xs : List α) : xs.toArray.pop = xs.dropLast.toArray := rfl

public theorem Array.eraseIdx.eq_def :
    type_of% (private_decl% @_root_.Array.eraseIdx.eq_def) := by
  intro α xs i bound
  obtain ⟨xs⟩ := xs
  split
  next h =>
    let swapped := xs.toArray.swap (i + 1) i h bound
    have eq := _root_.List.eraseIdx_toArray swapped.toList (i + 1)
      (by exact _root_.Array.eraseIdx._proof_1 xs.toArray i bound h)
    change xs.toArray.eraseIdx i bound = swapped.eraseIdx (i+1) _
    rw [_root_.List.eraseIdx_toArray]
    refine Eq.trans ?_ eq.symm
    dsimp only [swapped]
    rw [nativeSwap]
    exact congrArg List.toArray (neighbors xs i bound h)
  next h =>
    rw [_root_.List.eraseIdx_toArray, nativePop]
    exact congrArg List.toArray (lastErase xs i bound h)

/-- Dependent Boolean elimination whose constant-motive form reduces to the public monadic conditional. -/
public def List.anyM.match_1 (motive : Bool → Sort u) (b : Bool)
    (whenTrue : Unit → motive true) (whenFalse : Unit → motive false) : motive b :=
  if h : b = true then cast (congrArg motive h.symm) (whenTrue ())
  else cast (congrArg motive (Bool.eq_false_iff.mpr h).symm) (whenFalse ())

example (motive : Bool → Sort u) (b : Bool) (whenTrue : Unit → motive true)
    (whenFalse : Unit → motive false) :
    List.anyM.match_1 motive b whenTrue whenFalse =
      (private_decl% @_root_.List.anyM.match_1) motive b whenTrue whenFalse := by
  cases b <;> rfl

end OmegaChecks.InitPort.Alternatives
