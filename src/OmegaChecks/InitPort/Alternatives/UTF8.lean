module

public import OmegaChecks.InitPort.Alternatives.UTF8.Decode
import all OmegaChecks.InitPort.Alternatives.UTF8.Decode
import all Init.Data.String.Decode
import all Init.Data.String.Basic

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.two_pow_add_eq_or_of_lt : type_of% @_root_.Nat.two_pow_add_eq_or_of_lt := by
  intro i b small a
  let n := 2^i * a ||| b
  have parts := Nat.mod_add_div n (2^i)
  unfold n at parts
  rw [Nat.or_mod_two_pow, Nat.or_div_two_pow, Nat.mul_mod_right,
    Nat.mod_eq_of_lt small, Nat.zero_or, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt small, Nat.or_zero, Nat.add_comm] at parts
  exact parts

private theorem packedField (v : BitVec n) (s w : Nat) (tag : BitVec k) :
    (tag ++ v.extractLsb' s w).toNat = v.toNat / 2^s % 2^w + 2^w * tag.toNat := by
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mul_comm tag.toNat, ← _root_.Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
    Nat.add_comm]
private theorem packedByte (c : Char) {s w k : Nat} (tag : BitVec k) (size : k + w = 8)
    (v : Nat) (val : v = c.val.toNat / 2^s % 2^w + 2^w * tag.toNat) :
    (UInt8.ofNat v).toBitVec = (tag ++ c.val.toBitVec.extractLsb' s w).cast size := by
  apply BitVec.eq_of_toNat_eq
  change v % 256 = (tag ++ c.val.toBitVec.extractLsb' s w).toNat
  have eq : v = (tag ++ c.val.toBitVec.extractLsb' s w).toNat := val.trans (packedField ..).symm
  rw [eq, Nat.mod_eq_of_lt]
  have bound := (tag ++ c.val.toBitVec.extractLsb' s w).isLt
  exact Nat.lt_of_lt_of_eq bound (congrArg (2 ^ ·) size)

private def encodedBytes (c : Char) : Nat → List UInt8
  | 1 => [UInt8.ofNat c.val.toNat]
  | 2 => [UInt8.ofNat (c.val.toNat / 64 % 32 + 192),
      UInt8.ofNat (c.val.toNat % 64 + 128)]
  | 3 => [UInt8.ofNat (c.val.toNat / 4096 % 16 + 224),
      UInt8.ofNat (c.val.toNat / 64 % 64 + 128),
      UInt8.ofNat (c.val.toNat % 64 + 128)]
  | _ => [UInt8.ofNat (c.val.toNat / 262144 % 8 + 240),
      UInt8.ofNat (c.val.toNat / 4096 % 64 + 128),
      UInt8.ofNat (c.val.toNat / 64 % 64 + 128),
      UInt8.ofNat (c.val.toNat % 64 + 128)]

private theorem encodedBytes_of_size {c : Char} {n : Nat} (h : c.utf8Size = n) :
    String.utf8EncodeChar c = encodedBytes c n := by
  subst n
  rw [width_value]
  unfold String.utf8EncodeChar
  dsimp only
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

public theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 0) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 0 < 1) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 0) (w := 7) c 0#1 rfl _ (by
      have bound : c.val.toNat < 128 := Nat.lt_succ_of_le (_root_.Char.utf8Size_eq_one_iff.1 h)
      rw [Nat.div_one, Nat.mod_eq_of_lt bound]
      rfl))

public theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 0) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 0 < 2) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 6) (w := 5) c 6#3 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 1) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 1 < 2) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 0) (w := 6) c 2#2 rfl _ (by rw [Nat.div_one]; rfl))

public theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 0) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 0 < 3) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 12) (w := 4) c 14#4 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 1) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 1 < 3) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 6) (w := 6) c 2#2 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 2) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 2 < 3) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 0) (w := 6) c 2#2 rfl _ (by rw [Nat.div_one]; rfl))

public theorem String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 0) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 0 < 4) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 18) (w := 3) c 30#5 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 1) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 1 < 4) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 12) (w := 6) c 2#2 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 2) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 2 < 4) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 6) (w := 6) c 2#2 rfl _ rfl)

public theorem String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four) := fun {c} h =>
  (congrArg UInt8.toBitVec (List.getElem_of_eq (i := 3) (encodedBytes_of_size h)
    (Nat.lt_of_lt_of_eq (by decide : 3 < 4) ((_root_.String.length_utf8EncodeChar c).trans h).symm))).trans
    (packedByte (s := 0) (w := 6) c 2#2 rfl _ (by rw [Nat.div_one]; rfl))

private theorem consBytes {a b : UInt8} {xs ys : List UInt8} (h : a = b) (t : xs = ys) : a :: xs = b :: ys := h ▸ t ▸ rfl

private theorem maskedByte (x : UInt32) (w tag : Nat) (width : w ≤ 8)
    (fits : 2^w + 2^w * tag ≤ 256) :
    UInt8.ofNat (x.toNat % 2^w + 2^w * tag) =
      x.toUInt8 &&& UInt8.ofNat (2^w - 1) ||| UInt8.ofNat (2^w * tag) := by
  have small := Nat.mod_lt x.toNat (Nat.two_pow_pos w)
  have data := Nat.lt_of_lt_of_le (Nat.add_lt_add_right small (2^w * tag)) fits
  have tagBound : 2^w * tag < 256 := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.two_pow_pos w)) fits
  have maskBound : 2^w - 1 < 256 := Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos w)))
    (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) width)
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat_of_lt' data, UInt8.toNat_or, UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' maskBound,
    UInt8.toNat_ofNat_of_lt' tagBound, UInt32.toNat_toUInt8, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 width), Nat.or_comm, ← _root_.Nat.two_pow_add_eq_or_of_lt small,
    Nat.add_comm]

private theorem maskedShiftByte (x : UInt32) (s : UInt32) (w tag : Nat) (width : w ≤ 8)
    (fits : 2^w + 2^w * tag ≤ 256) :
    UInt8.ofNat (x.toNat / 2^(s.toNat % 32) % 2^w + 2^w * tag) =
      (x >>> s).toUInt8 &&& UInt8.ofNat (2^w - 1) ||| UInt8.ofNat (2^w * tag) := by
  have eq := maskedByte (x >>> s) w tag width fits
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at eq
  exact eq

public theorem String.utf8EncodeChar_eq_cons_cons : type_of% @_root_.String.utf8EncodeChar_eq_cons_cons := by
  intro c h
  rw [encodedBytes_of_size h]
  unfold encodedBytes
  apply consBytes
  · exact maskedShiftByte c.val 6 5 6 (by decide) (by decide)
  apply consBytes
  · exact maskedByte c.val 6 2 (by decide) (by decide)
  rfl

public theorem String.utf8EncodeChar_eq_cons_cons_cons : type_of% @_root_.String.utf8EncodeChar_eq_cons_cons_cons := by
  intro c h
  rw [encodedBytes_of_size h]
  unfold encodedBytes
  apply consBytes
  · exact maskedShiftByte c.val 12 4 14 (by decide) (by decide)
  apply consBytes
  · exact maskedShiftByte c.val 6 6 2 (by decide) (by decide)
  apply consBytes
  · exact maskedByte c.val 6 2 (by decide) (by decide)
  rfl

public theorem String.utf8EncodeChar_eq_cons_cons_cons_cons : type_of% @_root_.String.utf8EncodeChar_eq_cons_cons_cons_cons := by
  intro c h
  rw [encodedBytes_of_size h]
  unfold encodedBytes
  apply consBytes
  · exact maskedShiftByte c.val 18 3 30 (by decide) (by decide)
  apply consBytes
  · exact maskedShiftByte c.val 12 6 2 (by decide) (by decide)
  apply consBytes
  · exact maskedShiftByte c.val 6 6 2 (by decide) (by decide)
  apply consBytes
  · exact maskedByte c.val 6 2 (by decide) (by decide)
  rfl

public def String.utf8EncodeCharFast : type_of% @_root_.String.utf8EncodeCharFast :=
  @_root_.String.utf8EncodeChar

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.String.utf8EncodeCharFast.eq_1 (c : Char) :
    String.utf8EncodeCharFast c =
      (if c.val ≤ 0x7f then [c.val.toUInt8]
       else if c.val ≤ 0x7ff then
         [(c.val >>> 6).toUInt8 &&& 0x1f ||| 0xc0, c.val.toUInt8 &&& 0x3f ||| 0x80]
       else if c.val ≤ 0xffff then
         [(c.val >>> 12).toUInt8 &&& 0x0f ||| 0xe0, (c.val >>> 6).toUInt8 &&& 0x3f ||| 0x80,
           c.val.toUInt8 &&& 0x3f ||| 0x80]
       else
         [(c.val >>> 18).toUInt8 &&& 0x07 ||| 0xf0, (c.val >>> 12).toUInt8 &&& 0x3f ||| 0x80,
           (c.val >>> 6).toUInt8 &&& 0x3f ||| 0x80, c.val.toUInt8 &&& 0x3f ||| 0x80]) := by
  split
  · exact _root_.String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr ‹_›)
  · split
    · exact _root_.String.utf8EncodeChar_eq_cons_cons
        (Char.utf8Size_eq_two_iff.mpr ⟨UInt32.not_le.mp ‹_›, ‹_›⟩)
    · split
      · exact _root_.String.utf8EncodeChar_eq_cons_cons_cons
          (Char.utf8Size_eq_three_iff.mpr ⟨UInt32.not_le.mp ‹_›, ‹_›⟩)
      · exact _root_.String.utf8EncodeChar_eq_cons_cons_cons_cons
          (Char.utf8Size_eq_four_iff.mpr (UInt32.not_le.mp ‹_›))

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.String.utf8EncodeCharFast.eq_def :
    type_of% @_root_.OmegaChecks.InitPort.AlternativeEquations.String.utf8EncodeCharFast.eq_1 :=
  @_root_.OmegaChecks.InitPort.AlternativeEquations.String.utf8EncodeCharFast.eq_1

public theorem ByteArray.isValidUTF8_utf8Encode_singleton_append_iff :
    type_of% @_root_.ByteArray.isValidUTF8_utf8Encode_singleton_append_iff := by
  intro b c
  constructor
  · rintro ⟨l, eq⟩
    have lays := congrArg bytes eq
    rw [bytes_append] at lays
    obtain ⟨t, ht⟩ := remove_prefix [c] l (bytes b) lays
    exact ⟨t, ByteArray.ext (Array.ext' ht)⟩
  · exact fun valid => ByteArray.IsValidUTF8.append ByteArray.isValidUTF8_utf8Encode valid

private theorem valid_decoded_suffix (b : ByteArray) (fuel i : Nat) (hi : i ≤ b.size) (acc : Array Char)
    (room : b.size - i ≤ fuel) (ok : (ByteArray.utf8Decode?.go b i acc hi).isSome) :
    ByteArray.IsValidUTF8 (b.extract i b.size) := by
  induction fuel generalizing i acc with
  | zero =>
    have last := Nat.le_of_sub_eq_zero (Nat.le_zero.mp room)
    rw [ByteArray.extract_eq_empty_iff.2 (Nat.le_trans (Nat.min_le_left ..) last)]
    exact ByteArray.isValidUTF8_empty
  | succ n ih =>
    rw [ByteArray.utf8Decode?.go.eq_1] at ok
    by_cases ahead : i < b.size
    · rw [ite_eq_left ahead] at ok
      split at ok
      · cases ok
      · rename_i c code
        have fits := ByteArray.le_size_of_utf8DecodeChar?_eq_some code
        have smaller := Nat.sub_lt_sub_left ahead (Nat.lt_add_of_pos_right c.utf8Size_pos)
        have tail := ih (i + c.utf8Size) fits (acc.push c) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le smaller room)) ok
        have code' := _root_.ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract.symm.trans code
        have parts := _root_.ByteArray.eq_of_utf8DecodeChar?_eq_some code'
        rw [shift_from b _ _ hi, ← List.utf8Encode_singleton] at parts
        exact parts ▸ ByteArray.IsValidUTF8.append ByteArray.isValidUTF8_utf8Encode tail
    · rw [ByteArray.extract_eq_empty_iff.2 (Nat.le_trans (Nat.min_le_left ..) (Nat.le_of_not_lt ahead))]
      exact ByteArray.isValidUTF8_empty

public theorem ByteArray.isSome_utf8Decode?go_iff :
    type_of% (private_decl% @_root_.ByteArray.isSome_utf8Decode?go_iff) := by
  intro i b hi acc
  constructor
  · exact valid_decoded_suffix b (b.size - i) i hi acc (Nat.le_refl _)
  · rintro ⟨xs, suffix⟩
    rw [decode_encoded_tail xs i hi acc suffix]
    rfl

open _root_.ByteArray.utf8DecodeChar? in
private theorem encodingFromTwo {x y : UInt8} {c : Char}
    (h₁ : parseFirstByte x = .oneMore) (h₂ : assemble₂ x y = some c) :
    String.utf8EncodeChar c = [x, y] := by
  have hc := utf8Size_assemble₂ h₂
  have len := (String.length_utf8EncodeChar c).trans hc
  apply (List.eq_getElem_of_length_eq_two _ len).trans
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc,
      toBitVec_val_assemble₂ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_left]
    conv => rhs; rw [toBitVec_eq_of_parseFirstByte_eq_oneMore h₁]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc,
      toBitVec_val_assemble₂ _ h₂]
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
    conv => rhs; rw [toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₂_eq_some h₂)]
    rw [BitVec.extractLsb'_append_eq_right]
  rfl

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.assemble₂_eq_some_iff_utf8EncodeChar_eq :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₂_eq_some_iff_utf8EncodeChar_eq) := by
  intro x y c
  constructor
  · exact fun ⟨cls, ok⟩ => encodingFromTwo cls ok
  · intro eq
    have hc : c.utf8Size = 2 := (String.length_utf8EncodeChar c).symm.trans (congrArg List.length eq)
    have first : parseFirstByte x = .oneMore := by
      have encoded := parseFirstByte_utf8EncodeChar_eq_oneMore hc
      rw [List.getElem_of_eq eq] at encoded
      exact encoded
    refine ⟨first, ?_⟩
    have decoded := @_root_.ByteArray.utf8DecodeChar?_utf8EncodeChar_append ByteArray.empty c
    rw [eq, utf8DecodeChar?_append_eq_assemble₂ (l := [x, y]) (by rfl) first] at decoded
    exact decoded

open _root_.ByteArray.utf8DecodeChar? in
private theorem encodingFromThree {w x y : UInt8} {c : Char}
    (h₁ : parseFirstByte w = .twoMore) (h₂ : assemble₃ w x y = some c) :
    String.utf8EncodeChar c = [w, x, y] := by
  have hc := utf8Size_assemble₃ h₂
  have len := (String.length_utf8EncodeChar c).trans hc
  apply (List.eq_getElem_of_length_eq_three _ len).trans
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc,
      toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.append_assoc, BitVec.cast_eq, BitVec.extractLsb'_append_eq_left,
      ← toBitVec_eq_of_parseFirstByte_eq_twoMore h₁]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc,
      toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_right,
      ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_left h₂)]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc,
      toBitVec_val_assemble₃ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_right,
      ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_right h₂)]
  rfl

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.assemble₃_eq_some_iff_utf8EncodeChar_eq :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₃_eq_some_iff_utf8EncodeChar_eq) := by
  intro w x y c
  constructor
  · exact fun ⟨cls, ok⟩ => encodingFromThree cls ok
  · intro eq
    have hc : c.utf8Size = 3 := (String.length_utf8EncodeChar c).symm.trans (congrArg List.length eq)
    have first : parseFirstByte w = .twoMore := by
      have encoded := parseFirstByte_utf8EncodeChar_eq_twoMore hc
      rw [List.getElem_of_eq eq] at encoded
      exact encoded
    refine ⟨first, ?_⟩
    have decoded := @_root_.ByteArray.utf8DecodeChar?_utf8EncodeChar_append ByteArray.empty c
    rw [eq, utf8DecodeChar?_append_eq_assemble₃ (l := [w, x, y]) (by rfl) first] at decoded
    exact decoded

open _root_.ByteArray.utf8DecodeChar? in
private theorem encodingFromFour {w x y z : UInt8} {c : Char}
    (h₁ : parseFirstByte w = .threeMore) (h₂ : assemble₄ w x y z = some c) :
    String.utf8EncodeChar c = [w, x, y, z] := by
  have hc := utf8Size_assemble₄ h₂
  have len := (String.length_utf8EncodeChar c).trans hc
  apply (List.eq_getElem_of_length_eq_four _ len).trans
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hc,
      toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.append_assoc, BitVec.cast_eq, BitVec.append_assoc, BitVec.cast_eq,
      BitVec.extractLsb'_append_eq_left,
      ← toBitVec_eq_of_parseFirstByte_eq_threeMore h₁]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc,
      toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
      BitVec.extractLsb'_append_eq_right,
      ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_left h₂)]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc,
      toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_right,
      ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_middle h₂)]
  apply consBytes
  · apply UInt8.eq_of_toBitVec_eq
    rw [_root_.String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc,
      toBitVec_val_assemble₄ _ h₂, BitVec.extractLsb'_setWidth_of_le (by decide),
      BitVec.extractLsb'_append_eq_right,
      ← toBitVec_eq_of_isInvalidContinuationByte_eq_false (isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_right h₂)]
  rfl

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq) := by
  intro w x y z c
  constructor
  · exact fun ⟨cls, ok⟩ => encodingFromFour cls ok
  · intro eq
    have hc : c.utf8Size = 4 := (String.length_utf8EncodeChar c).symm.trans (congrArg List.length eq)
    have first : parseFirstByte w = .threeMore := by
      have encoded := parseFirstByte_utf8EncodeChar_eq_threeMore hc
      rw [List.getElem_of_eq eq] at encoded
      exact encoded
    refine ⟨first, ?_⟩
    have decoded := @_root_.ByteArray.utf8DecodeChar?_utf8EncodeChar_append ByteArray.empty c
    rw [eq, utf8DecodeChar?_append_eq_assemble₄ (l := [w, x, y, z]) (by rfl) first] at decoded
    exact decoded

private theorem splitMaskedByte (b mask val : UInt8) (w : Nat) (tag : BitVec k) (size : k + w = 8)
    (maskTop : mask.toNat / 2^w = 2^k - 1) (tagTop : val.toNat / 2^w = tag.toNat)
    (cls : b &&& mask = val) : b.toBitVec = (tag ++ b.toBitVec.setWidth w).cast size := by
  have top := congrArg (fun x : UInt8 => x.toNat / 2^w) cls
  change (b &&& mask).toNat / 2^w = val.toNat / 2^w at top
  rw [UInt8.toNat_and, Nat.and_div_two_pow, maskTop, tagTop, Nat.and_two_pow_sub_one_eq_mod] at top
  have hsize : b.toNat < 2^w * 2^k := by
    rw [← Nat.pow_add, Nat.add_comm, size]
    exact b.toNat_lt_size
  have upper : b.toNat / 2^w < 2^k := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    ((Nat.mul_comm ..) ▸ hsize)
  rw [Nat.mod_eq_of_lt upper] at top
  apply BitVec.eq_of_toNat_eq
  change b.toNat = (tag ++ b.toBitVec.setWidth w).toNat
  rw [BitVec.toNat_append, BitVec.toNat_setWidth, UInt8.toNat_toBitVec, Nat.shiftLeft_eq, Nat.mul_comm tag.toNat,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), ← top, Nat.add_comm, Nat.mod_add_div]

open _root_.ByteArray.utf8DecodeChar? in
private instance : DecidableEq FirstByte := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (fun h => nomatch h)

/-- Check a property of first-byte tags on every member of the byte type. -/
private theorem everyByte (p : UInt8 → Prop) [DecidablePred p]
    (certificate : decide (∀ i : Fin 256, p ⟨⟨i⟩⟩) = true) (b : UInt8) : p b :=
  of_decide_eq_true certificate b.toBitVec.toFin

section
open _root_.ByteArray.utf8DecodeChar?
set_option maxRecDepth 4096

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_oneMore_iff :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_oneMore_iff) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .oneMore ↔ b &&& 0xe0 = 0xc0) (by decide) b

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_oneMore_iff_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_oneMore_iff_toBitVec) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .oneMore ↔ b.toBitVec.extractLsb' 5 3 = 0b110#3) (by decide) b

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_twoMore_iff :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_twoMore_iff) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .twoMore ↔ b &&& 0xf0 = 0xe0) (by decide) b

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_twoMore_iff_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_twoMore_iff_toBitVec) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .twoMore ↔ b.toBitVec.extractLsb' 4 4 = 0b1110#4) (by decide) b

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_threeMore_iff :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_threeMore_iff) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .threeMore ↔ b &&& 0xf8 = 0xf0) (by decide) b

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_eq_threeMore_iff_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_eq_threeMore_iff_toBitVec) := by
  intro b
  exact everyByte (fun b => parseFirstByte b = .threeMore ↔ b.toBitVec.extractLsb' 3 5 = 0b11110#5) (by decide) b

public theorem UInt8.isUTF8FirstByte_iff_parseFirstByte_ne_invalid :
    type_of% (private_decl% @_root_.UInt8.isUTF8FirstByte_iff_parseFirstByte_ne_invalid) := by
  intro b
  exact everyByte (fun b => b.IsUTF8FirstByte ↔ parseFirstByte b ≠ .invalid) (by decide) b

end

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_done :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_done) := by
  intro b h
  apply splitMaskedByte b 128 0 7 0#1 rfl rfl rfl
  unfold parseFirstByte at h
  repeat' split at h
  all_goals first | exact of_decide_eq_true (by assumption) | cases h

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_oneMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_oneMore) := by
  intro b h
  apply splitMaskedByte b 224 192 5 6#3 rfl rfl rfl
  unfold parseFirstByte at h
  repeat' split at h
  all_goals first | exact of_decide_eq_true (by assumption) | cases h

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_twoMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_twoMore) := by
  intro b h
  apply splitMaskedByte b 240 224 4 14#4 rfl rfl rfl
  unfold parseFirstByte at h
  repeat' split at h
  all_goals first | exact of_decide_eq_true (by assumption) | cases h

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_threeMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_eq_of_parseFirstByte_eq_threeMore) := by
  intro b h
  apply splitMaskedByte b 248 240 3 30#5 rfl rfl rfl
  unfold parseFirstByte at h
  repeat' split at h
  all_goals first | exact of_decide_eq_true (by assumption) | cases h

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.toBitVec_eq_of_isInvalidContinuationByte_eq_false :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_eq_of_isInvalidContinuationByte_eq_false) := by
  intro b h
  apply splitMaskedByte b 192 128 6 2#2 rfl rfl rfl
  exact bne_eq_false_iff_eq.1 h

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₂_eq_some :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₂_eq_some) := by
  intro w x c someEq
  cases invalid : isInvalidContinuationByte x with
  | false => rfl
  | true =>
    unfold assemble₂ at someEq
    rw [invalid] at someEq
    simp only [ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_left :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_left) := by
  intro w x y c someEq
  cases invalid : isInvalidContinuationByte x with
  | false => rfl
  | true =>
    unfold assemble₃ at someEq
    rw [invalid] at someEq
    simp only [Bool.true_or, ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_right :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₃_eq_some_right) := by
  intro w x y c someEq
  cases invalid : isInvalidContinuationByte y with
  | false => rfl
  | true =>
    unfold assemble₃ at someEq
    rw [invalid] at someEq
    simp only [Bool.or_true, ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_left :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_left) := by
  intro w x y z c someEq
  cases invalid : isInvalidContinuationByte x with
  | false => rfl
  | true =>
    unfold assemble₄ at someEq
    rw [invalid] at someEq
    simp only [Bool.true_or, ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_middle :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_middle) := by
  intro w x y z c someEq
  cases invalid : isInvalidContinuationByte y with
  | false => rfl
  | true =>
    unfold assemble₄ at someEq
    rw [invalid] at someEq
    simp only [Bool.or_true, Bool.true_or, ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_right :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_eq_false_of_assemble₄_eq_some_right) := by
  intro w x y z c someEq
  cases invalid : isInvalidContinuationByte z with
  | false => rfl
  | true =>
    unfold assemble₄ at someEq
    rw [invalid] at someEq
    simp only [Bool.or_true, ite_true] at someEq
    cases someEq

open _root_.ByteArray.utf8DecodeChar? in
private theorem encodingFromOne {w : UInt8} {c : Char}
    (cls : parseFirstByte w = .done) (ok : assemble₁ w cls = some c) :
    String.utf8EncodeChar c = [w] := by
  have size := utf8Size_assemble₁ ok
  rw [String.utf8EncodeChar_eq_singleton size]
  exact (congrArg (fun a : Char => [a.val.toUInt8]) (Option.some.inj ok).symm).trans
    (congrArg (fun b : UInt8 => [b]) (UInt8.toUInt8_toUInt32 w))

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.assemble₁_eq_some_iff_utf8EncodeChar_eq :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₁_eq_some_iff_utf8EncodeChar_eq) := by
  intro w c
  constructor
  · exact fun ⟨cls, ok⟩ => encodingFromOne cls ok
  · intro eq
    have size : c.utf8Size = 1 := (String.length_utf8EncodeChar c).symm.trans (congrArg List.length eq)
    have cls : parseFirstByte w = .done := by
      have encoded := parseFirstByte_utf8EncodeChar_eq_done size
      rw [List.getElem_of_eq eq] at encoded
      exact encoded
    refine ⟨cls, ?_⟩
    have decoded := @_root_.ByteArray.utf8DecodeChar?_utf8EncodeChar_append ByteArray.empty c
    rw [eq, utf8DecodeChar?_append_eq_assemble₁ (l := [w]) rfl cls] at decoded
    exact decoded

open _root_.ByteArray.utf8DecodeChar? in
public theorem String.toByteArray_utf8EncodeChar_of_utf8DecodeChar?_eq_some :
    type_of% @_root_.String.toByteArray_utf8EncodeChar_of_utf8DecodeChar?_eq_some := by
  intro b c decoded
  have fits := utf8Size_le_of_utf8DecodeChar?_eq_some decoded
  have front := Nat.lt_of_lt_of_le c.utf8Size_pos fits
  rcases c.utf8Size_eq with size | size | size | size
  · have room : 1 ≤ b.size := size ▸ fits
    have cls := parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some decoded size front
    have assembled := (utf8DecodeChar?_eq_assemble₁ room cls).symm.trans decoded
    have bytes := encodingFromOne cls assembled
    rw [size, ByteArray.extract_add_one (i := 0) room]
    exact congrArg List.toByteArray bytes
  · have room : 2 ≤ b.size := size ▸ fits
    have cls := parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some decoded size front
    have assembled := (utf8DecodeChar?_eq_assemble₂ room cls).symm.trans decoded
    have bytes := encodingFromTwo cls assembled
    rw [size, ByteArray.extract_add_two (i := 0) room]
    exact congrArg List.toByteArray bytes
  · have room : 3 ≤ b.size := size ▸ fits
    have cls := parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some decoded size front
    have assembled := (utf8DecodeChar?_eq_assemble₃ room cls).symm.trans decoded
    have bytes := encodingFromThree cls assembled
    rw [size, ByteArray.extract_add_three (i := 0) room]
    exact congrArg List.toByteArray bytes
  · have room : 4 ≤ b.size := size ▸ fits
    have cls := parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some decoded size front
    have assembled := (utf8DecodeChar?_eq_assemble₄ room cls).symm.trans decoded
    have bytes := encodingFromFour cls assembled
    rw [size, ByteArray.extract_add_four (i := 0) room]
    exact congrArg List.toByteArray bytes

public theorem String.toList_ofList : type_of% @_root_.String.toList_ofList := by
  intro l
  have ok : l.utf8Encode.utf8Decode?.isSome := by rw [_root_.List.utf8Decode?_utf8Encode]; rfl
  have array := Option.get_of_eq_some ok (@_root_.List.utf8Decode?_utf8Encode l)
  exact (congrArg Array.toList array).trans List.toList_toArray

public theorem String.ofList_toList : type_of% @_root_.String.ofList_toList := by
  intro s
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  exact congrArg String.ofList (@_root_.String.toList_ofList l)

private def scalarClass : Nat → ByteArray.utf8DecodeChar?.FirstByte
  | 1 => .done
  | 2 => .oneMore
  | 3 => .twoMore
  | 4 => .threeMore
  | _ => .invalid

open _root_.ByteArray.utf8DecodeChar? in
private theorem class_of_decoded {b : ByteArray} {i : Nat} {c : Char}
    (valid : i < b.size) (code : b.utf8DecodeChar? i = some c) :
    parseFirstByte b[i] = scalarClass c.utf8Size := by
  revert code
  fun_cases ByteArray.utf8DecodeChar? with
  | case1 | case4 | case6 | case8 | case9 => intro h; cases h
  | case2 => intro h; rw [utf8Size_assemble₁ h]; assumption
  | case3 => intro h; rw [utf8Size_assemble₂ h]; assumption
  | case5 => intro h; rw [utf8Size_assemble₃ h]; assumption
  | case7 => intro h; rw [utf8Size_assemble₄ h]; assumption

public theorem parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some :
    type_of% (private_decl% @_root_.parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some) :=
  fun h size valid => (class_of_decoded valid h).trans (congrArg scalarClass size)

public theorem parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some :
    type_of% (private_decl% @_root_.parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some) :=
  fun h size valid => (class_of_decoded valid h).trans (congrArg scalarClass size)

public theorem parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some :
    type_of% (private_decl% @_root_.parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some) :=
  fun h size valid => (class_of_decoded valid h).trans (congrArg scalarClass size)

public theorem parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some :
    type_of% (private_decl% @_root_.parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some) :=
  fun h size valid => (class_of_decoded valid h).trans (congrArg scalarClass size)

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.le_val_assemble₄ :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.le_val_assemble₄) := by
  intro w x y z c
  fun_cases assemble₄ w x y z with
  | case1 | case2 | case3 => intro h; cases h
  | case4 =>
    intro ok
    cases Option.some.inj ok
    apply (UInt32.ofNat_lt_iff (by decide : 65535 < 2 ^ 32)).2
    have lower := (UInt32.ofNat_le_iff (by decide : 65536 < 2 ^ 32)).1
      (UInt32.not_lt.1 (by assumption))
    have carry : (65535 : Nat).succ = 65536 := succ_lowMask 16
    exact Nat.lt_of_succ_le (carry.symm ▸ lower)

public theorem BitVec.append_assoc : type_of% @_root_.BitVec.append_assoc := by
  intro w₁ w₂ w₃ x₁ x₂ x₃
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc]

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar? :
    type_of% @_root_.ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar? := by
  intro b i
  unfold ByteArray.validateUTF8At ByteArray.utf8DecodeChar?
  split
  · split
    · rfl
    · exact verify₁_eq_isSome_assemble₁
    · split
      · exact verify₂_eq_isSome_assemble₂
      · rfl
    · split
      · exact verify₃_eq_isSome_assemble₃
      · rfl
    · split
      · exact verify₄_eq_isSome_assemble₄
      · rfl
  · rfl

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.verify₃_eq_isSome_assemble₃ :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.verify₃_eq_isSome_assemble₃) := by
  intro w x y
  unfold verify₃ assemble₃
  dsimp only
  split
  · rfl
  · split <;> rename_i cut
    · exact decide_eq_false (fun ok => UInt32.not_le.mpr cut ok.1)
    · split <;> rename_i gap
      · exact decide_eq_false (fun ok => ok.2.elim (UInt32.not_lt.mpr gap.1) (UInt32.not_lt.mpr gap.2))
      · apply decide_eq_true
        refine ⟨UInt32.not_lt.mp cut, ?_⟩
        by_cases before : (assemble₃Unchecked w x y) < 0xd800
        · exact Or.inl before
        · exact Or.inr (UInt32.not_le.mp (fun below => gap ⟨UInt32.not_lt.mp before, below⟩))

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?.verify₄_eq_isSome_assemble₄ :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.verify₄_eq_isSome_assemble₄) := by
  intro w x y z
  unfold verify₄ assemble₄
  dsimp only
  split
  · rfl
  · split <;> rename_i cut
    · exact decide_eq_false (fun ok => Nat.not_le_of_lt cut ok.1)
    · split <;> rename_i last
      · exact decide_eq_false (fun ok => Nat.not_le_of_lt last ok.2)
      · exact decide_eq_true ⟨Nat.le_of_not_lt cut, Nat.le_of_not_lt last⟩

private theorem validationAtEq (b : ByteArray) {i j : Nat} (pos : i = j) (hi : i ≤ b.size) (hj : j ≤ b.size) :
    ByteArray.validateUTF8.go b i hi = ByteArray.validateUTF8.go b j hj := by
  cases pos
  rfl

private theorem validation_agrees (b : ByteArray) (fuel i : Nat) (hi : i ≤ b.size) (acc : Array Char)
    (room : b.size - i ≤ fuel) :
    (ByteArray.utf8Decode?.go b i acc hi).isSome = ByteArray.validateUTF8.go b i hi := by
  induction fuel generalizing i acc with
  | zero =>
    have stop := Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero (Nat.le_zero.mp room))
    rw [ByteArray.utf8Decode?.go.eq_1, ByteArray.validateUTF8.go.eq_def, ite_eq_right stop, dite_eq_right stop]
    rfl
  | succ n ih =>
    rw [ByteArray.utf8Decode?.go.eq_1, ByteArray.validateUTF8.go.eq_def]
    by_cases ahead : i < b.size
    · rw [ite_eq_left ahead, dite_eq_left ahead]
      split <;> rename_i code
      · split <;> rename_i valid
        · rfl
        · have invalid := (ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar? (b := b) (i := i)).trans
            (congrArg Option.isSome code)
          cases valid.symm.trans invalid
      · rename_i c
        split <;> rename_i valid
        · have live := (ByteArray.validateUTF8At_eq_isSome_utf8DecodeChar? (b := b) (i := i)).trans
            (congrArg Option.isSome code)
          cases valid.symm.trans live
        · have witness : (b.utf8DecodeChar? i).isSome := (congrArg Option.isSome code).trans rfl
          have head : b.utf8DecodeChar i witness = c := Option.get_of_eq_some witness code
          have width := (congrArg Char.utf8Size head.symm).trans (ByteArray.utf8Size_utf8DecodeChar (h := witness))
          have next := ByteArray.le_size_of_utf8DecodeChar?_eq_some code
          have smaller := Nat.sub_lt_sub_left ahead (Nat.lt_add_of_pos_right c.utf8Size_pos)
          exact (ih (i + c.utf8Size) next (acc.push c) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le smaller room))).trans
            (validationAtEq b (congrArg (i + ·) width) _ _)
    · rw [ite_eq_right ahead, dite_eq_right ahead]
      rfl

public theorem ByteArray.isSome_utf8Decode?Go_eq_validateUTF8Go :
    type_of% @_root_.ByteArray.isSome_utf8Decode?Go_eq_validateUTF8Go :=
  fun {b i acc hi} => validation_agrees b (b.size - i) i hi acc (Nat.le_refl _)

end OmegaChecks.InitPort.Alternatives
