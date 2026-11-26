module
public import Init.Data.String.Pattern.String
public import Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.ByteArray.Lemmas
import all Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.String.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Pattern.String
namespace OmegaChecks.InitPort.Alternatives
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

end OmegaChecks.InitPort.Alternatives
