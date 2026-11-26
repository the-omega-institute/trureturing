module
import all Init.Data.String.Decode
import all Init.Data.String.Basic
import all Init.Data.ByteArray.Lemmas
import all Init.Data.BitVec.Lemmas
import all Init.Data.Nat.Bitwise.Lemmas
import all Init.Data.Nat.Mod

/-! The leading and continuation byte ranges of UTF-8 code points. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem BitVec.ushiftRight._proof_3 : type_of% @_root_.BitVec.ushiftRight._proof_3 := by
  intro n x s
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le ..) x.isLt

public theorem BitVec.extractLsb'_append_eq_left : type_of% @_root_.BitVec.extractLsb'_append_eq_left := by
  intro w v a b
  apply BitVec.toNat_inj.mp
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight, Nat.shiftRight_eq_zero _ _ b.isLt, Nat.or_zero, Nat.mod_eq_of_lt a.isLt]

public theorem Nat.testBit_mod_two_pow : type_of% @_root_.Nat.testBit_mod_two_pow := by
  intro x j i
  by_cases lt : i < j
  · rw [decide_eq_true lt, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have power : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt lt)]
    have dvd : 2 ∣ 2 ^ (j - i) := Nat.pow_dvd_pow 2 (Nat.sub_pos_of_lt lt)
    rw [power, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ dvd]
  · rw [decide_eq_false lt, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt lt)))

public theorem Nat.bitwise_mod_two_pow : type_of% @_root_.Nat.bitwise_mod_two_pow := by
  intro f x y n zero
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_bitwise zero, Nat.testBit_bitwise zero,
    Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  cases decide (i < n) with
  | false => exact zero.symm
  | true => rfl

private theorem highestBits {i k tag mask : Nat} (low : i < 2 ^ k)
    (zero : mask % (2 ^ k) = 0) :
    (i + 2 ^ k * tag) &&& mask = 2 ^ k * (tag &&& (mask / 2 ^ k)) := by
  let n := i + 2 ^ k * tag
  calc
    _ = (n &&& mask) % 2 ^ k + 2 ^ k * ((n &&& mask) / 2 ^ k) := (Nat.mod_add_div ..).symm
    _ = _ := by
      rw [Nat.and_mod_two_pow, zero, Nat.and_zero, Nat.zero_add, Nat.and_div_two_pow]
      change _ * ((i + 2 ^ k * tag) / 2 ^ k &&& _) = _
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt low, Nat.zero_add]

private theorem firstAscii (x : Fin 128) : (UInt8.ofNat x.val).IsUTF8FirstByte := by
  apply Or.inl
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_trans x.isLt (by decide))]
  exact highestBits (tag := 0) (mask := 128) (k := 7) x.isLt rfl

private theorem firstTwo (x : Fin 32) : (UInt8.ofNat (x.val + 192)).IsUTF8FirstByte := by
  apply Or.inr ∘ Or.inl
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.add_lt_add_right x.isLt 192) (by decide))]
  exact highestBits (tag := 6) (mask := 224) (k := 5) x.isLt rfl

private theorem firstThree (x : Fin 16) : (UInt8.ofNat (x.val + 224)).IsUTF8FirstByte := by
  apply Or.inr ∘ Or.inr ∘ Or.inl
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.add_lt_add_right x.isLt 224) (by decide))]
  exact highestBits (tag := 14) (mask := 240) (k := 4) x.isLt rfl

private theorem firstFour (x : Fin 8) : (UInt8.ofNat (x.val + 240)).IsUTF8FirstByte := by
  apply Or.inr ∘ Or.inr ∘ Or.inr
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.add_lt_add_right x.isLt 240) (by decide))]
  exact highestBits (tag := 30) (mask := 248) (k := 3) x.isLt rfl

private theorem continuation (x : Fin 64) : ¬ (UInt8.ofNat (x.val + 128)).IsUTF8FirstByte := by
  have high : (x.val + 128) / 2 ^ 6 = 2 := by
    change (x.val + 2 ^ 6 * 2) / 2 ^ 6 = 2
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 6), Nat.div_eq_of_lt x.isLt]
  have different {mask required : UInt8} (ne : 2 &&& (mask.toNat / 2 ^ 6) ≠ required.toNat / 2 ^ 6) :
      UInt8.ofNat (x.val + 128) &&& mask ≠ required := by
    intro eq
    have top := congrArg (fun v : UInt8 => v.toNat / 2 ^ 6) eq
    change ((UInt8.ofNat (x.val + 128) &&& mask).toNat / 2 ^ 6) = _ at top
    rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.add_lt_add_right x.isLt 128) (by decide)),
      Nat.and_div_two_pow, high] at top
    exact ne top
  rintro (h | h | h | h) <;> exact different (by decide) h

private def byteOffsets (bs : List UInt8) := ∀ (i : Nat) (h : i < bs.length), bs[i].IsUTF8FirstByte ↔ i = 0

public theorem UInt8.isUTF8FirstByte_getElem_utf8EncodeChar :
    type_of% @_root_.UInt8.isUTF8FirstByte_getElem_utf8EncodeChar := by
  intro c
  change byteOffsets (String.utf8EncodeChar c)
  unfold String.utf8EncodeChar
  dsimp only
  split
  · rename_i ascii
    intro i hi
    cases i with
    | zero => exact ⟨fun _ => rfl, fun _ => firstAscii ⟨_, Nat.lt_succ_of_le ascii⟩⟩
    | succ i => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hi)).elim
  · split
    · intro i hi
      match i, hi with
      | 0, _ => exact ⟨fun _ => rfl, fun _ => firstTwo ⟨_, Nat.mod_lt _ (by decide)⟩⟩
      | 1, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩
    · split
      · intro i hi
        match i, hi with
        | 0, _ => exact ⟨fun _ => rfl, fun _ => firstThree ⟨_, Nat.mod_lt _ (by decide)⟩⟩
        | 1, _ | 2, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩
      · intro i hi
        match i, hi with
        | 0, _ => exact ⟨fun _ => rfl, fun _ => firstFour ⟨_, Nat.mod_lt _ (by decide)⟩⟩
        | 1, _ | 2, _ | 3, _ => exact ⟨fun h => (continuation ⟨_, Nat.mod_lt _ (by decide)⟩ h).elim, by intro h; cases h⟩

public theorem String.length_utf8EncodeChar : type_of% @_root_.String.length_utf8EncodeChar := by
  intro c
  unfold String.utf8EncodeChar Char.utf8Size
  dsimp only
  repeat' split
  all_goals first | rfl | contradiction

public theorem List.isUTF8FirstByte_getElem_utf8Encode_singleton :
    type_of% @_root_.List.isUTF8FirstByte_getElem_utf8Encode_singleton := by
  intro c i
  rw [List.utf8Encode_singleton]
  intro hi
  rw [List.getElem_toByteArray]
  exact UInt8.isUTF8FirstByte_getElem_utf8EncodeChar

public theorem ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero :
    type_of% @_root_.ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero := by
  rintro b ⟨l, rfl⟩
  cases l with
  | nil => exact fun h => (Nat.not_lt_zero _ h).elim
  | cons c l =>
    rw [List.utf8Encode_cons]
    intro h
    have pos : 0 < [c].utf8Encode.size := by
      rw [List.utf8Encode_singleton, List.size_toByteArray, String.length_utf8EncodeChar]
      exact c.utf8Size_pos
    rw [ByteArray.getElem_append_left pos]
    exact List.isUTF8FirstByte_getElem_utf8Encode_singleton.mpr rfl

public theorem ByteArray.getElem_append_right._proof_2 :
    type_of% @_root_.ByteArray.getElem_append_right._proof_2 := by
  intro i a b h hle
  have sum : i < a.size + b.size := ByteArray.size_append ▸ h
  have reduced : a.size + (i - a.size) < a.size + b.size := by
    rw [Nat.add_sub_of_le hle]
    exact sum
  exact Nat.add_lt_add_iff_left.mp reduced

private def firstAt (b : ByteArray) (i : Nat) := ∃ h : i < b.size, b[i].IsUTF8FirstByte

private theorem splitAtFirst (l : List Char) (i : Nat) (hi : i < l.utf8Encode.size)
    (first : l.utf8Encode[i].IsUTF8FirstByte) :
    ∃ a b : List Char, l = a ++ b ∧ i = a.utf8Encode.size := by
  induction l generalizing i with
  | nil => exact (Nat.not_lt_zero _ hi).elim
  | cons c l ih =>
    have atPos : firstAt (c :: l).utf8Encode i := ⟨hi, first⟩
    rw [List.utf8Encode_cons] at atPos
    obtain ⟨_, first⟩ := atPos
    by_cases left : i < [c].utf8Encode.size
    · rw [ByteArray.getElem_append_left left] at first
      exact ⟨[], c :: l, rfl, List.isUTF8FirstByte_getElem_utf8Encode_singleton.mp first⟩
    · have le := Nat.le_of_not_lt left
      rw [ByteArray.getElem_append_right le] at first
      obtain ⟨a, b, rfl, eq⟩ := ih _ _ first
      refine ⟨c :: a, b, rfl, ?_⟩
      rw [List.utf8Encode_cons, ByteArray.size_append, ← eq, Nat.add_sub_of_le le]

public theorem String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize :
    type_of% @_root_.String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize := by
  intro s off valid
  exact String.Pos.isValidUTF8_extract ⟨off, valid⟩ s.endPos

public theorem String.Pos.Raw.isValid_iff_isUTF8FirstByte :
    type_of% @_root_.String.Pos.Raw.isValid_iff_isUTF8FirstByte := by
  intro s p
  constructor
  · intro valid
    by_cases eq : p = s.rawEndPos
    · exact Or.inl eq
    · have lt := Nat.lt_of_le_of_ne valid.le_utf8ByteSize (fun h => eq (String.Pos.Raw.ext h))
      have suffix := String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize valid
      have pos : 0 < (s.toByteArray.extract p.byteIdx s.utf8ByteSize).size := by
        rw [ByteArray.size_extract, String.size_toByteArray, Nat.min_self]
        exact Nat.sub_pos_of_lt lt
      have first := ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero suffix pos
      rw [ByteArray.getElem_extract] at first
      exact Or.inr ⟨lt, first⟩
  · rintro (rfl | ⟨lt, first⟩)
    · exact s.endPos.isValid
    · apply _root_.String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero.mpr
      refine ⟨Nat.le_of_lt lt, ?_⟩
      obtain ⟨l, eq⟩ := s.isValidUTF8
      change s.toByteArray[p.byteIdx].IsUTF8FirstByte at first
      have atPos : firstAt s.toByteArray p.byteIdx := ⟨lt, first⟩
      rw [eq] at atPos ⊢
      obtain ⟨_, first⟩ := atPos
      obtain ⟨a, b, rfl, off⟩ := splitAtFirst _ _ _ first
      rw [List.utf8Encode_append, ByteArray.extract_append_eq_left off]
      exact ⟨a, rfl⟩

end OmegaChecks.InitPort.Alternatives
