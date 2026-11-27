module
import OmegaChecks.InitPort.Alternatives.ByteArray
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

public theorem BitVec.extractLsb'_append_eq_of_le :
    type_of% @_root_.BitVec.extractLsb'_append_eq_of_le := by
  intro v w hi lo start len bound
  apply BitVec.toNat_inj.mp
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_append]
  have high : (hi.toNat <<< w ||| lo.toNat) >>> w = hi.toNat := by
    rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight, Nat.shiftRight_eq_zero _ _ lo.isLt, Nat.or_zero]
  have offset : start = w + (start - w) := (Nat.add_sub_of_le bound).symm
  exact congrArg (fun n => n % 2 ^ len)
    (((congrArg (fun pos => (hi.toNat <<< w ||| lo.toNat) >>> pos) offset).trans (Nat.shiftRight_add ..)).trans
      (congrArg (· >>> (start - w)) high))

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

public theorem Nat.testBit_two_pow_sub_one : type_of% @_root_.Nat.testBit_two_pow_sub_one := by
  intro n i
  induction n generalizing i with
  | zero =>
    change Nat.testBit 0 i = _
    rw [Nat.zero_testBit, decide_eq_false (Nat.not_lt_zero _)]
  | succ n ih =>
    have mask : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have pred : (2 ^ n - 1).succ = 2 ^ n := Nat.succ_pred_eq_of_pos (Nat.two_pow_pos n)
      rw [Nat.pow_succ, ← pred, Nat.succ_mul, Nat.mul_comm]
      rfl
    rw [mask]
    cases i with
    | zero =>
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_one, Nat.mul_add_mod_self_left,
        decide_eq_true (Nat.zero_lt_succ _)]
      rfl
    | succ i =>
      rw [Nat.testBit_succ, Nat.add_comm (2 * (2 ^ n - 1)) 1, Nat.add_mul_div_left _ _ (by decide)]
      change Nat.testBit (0 + (2 ^ n - 1)) i = _
      rw [Nat.zero_add, ih]
      by_cases lt : i < n
      · rw [decide_eq_true lt, decide_eq_true (Nat.succ_lt_succ lt)]
      · rw [decide_eq_false lt, decide_eq_false (fun h => lt (Nat.lt_of_succ_lt_succ h))]

public theorem Nat.and_zero : type_of% @_root_.Nat.and_zero := by
  intro n
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit, Bool.and_false]

public theorem Nat.zero_and : type_of% @_root_.Nat.zero_and := by
  intro n
  exact (Nat.and_comm 0 n).trans (Nat.and_zero n)

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

public theorem String.Pos.Raw.isValidUTF8_extract_iff : type_of% @_root_.String.Pos.Raw.isValidUTF8_extract_iff := by
  intro s p q le upper
  constructor
  · intro valid
    by_cases eq : p = q
    · exact Or.inl eq
    · have lt : p.byteIdx < q.byteIdx :=
        Nat.lt_of_le_of_ne le (fun eqIdx => eq (String.Pos.Raw.ext eqIdx))
      have nonempty : 0 < (s.toByteArray.extract p.byteIdx q.byteIdx).size := by
        rw [ByteArray.size_extract, Nat.min_eq_left (show q.byteIdx ≤ s.toByteArray.size from upper)]
        exact Nat.sub_pos_of_lt lt
      have first := ByteArray.IsValidUTF8.isUTF8FirstByte_getElem_zero valid nonempty
      rw [ByteArray.getElem_extract] at first
      have hp := String.Pos.Raw.isValid_iff_isUTF8FirstByte.mpr (Or.inr ⟨Nat.lt_of_lt_of_le lt upper, first⟩)
      refine Or.inr ⟨hp, _root_.String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero.mpr ⟨upper, ?_⟩⟩
      rw [ByteArray.extract_eq_extract_append_extract p.byteIdx (Nat.zero_le _) le]
      exact hp.isValidUTF8_extract_zero.append valid
  · rintro (rfl | ⟨hp, hq⟩)
    · rw [ByteArray.extract_same]
      exact ByteArray.isValidUTF8_empty
    · exact _root_.String.Pos.isValidUTF8_extract ⟨p, hp⟩ ⟨q, hq⟩

public theorem String.Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize :
    type_of% @_root_.String.Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize := by
  intro s p
  constructor
  · intro valid
    exact ⟨valid.le_rawEndPos, String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize valid⟩
  · rintro ⟨le, utf8⟩
    obtain eq | ⟨hp, _⟩ := (String.Pos.Raw.isValidUTF8_extract_iff p s.rawEndPos le (Nat.le_refl _)).mp utf8
    · exact eq ▸ s.endPos.isValid
    · exact hp

public theorem String.Pos.Raw.isValid_push : type_of% @_root_.String.Pos.Raw.isValid_push := by
  intro s c p
  constructor
  · intro valid
    rw [← _root_.String.append_singleton] at valid
    obtain inOriginal | ⟨lower, tail⟩ := _root_.String.Pos.Raw.isValid_append.mp valid
    · exact Or.inl inOriginal
    · have low : s.utf8ByteSize ≤ p.byteIdx := lower
      have restore := Nat.sub_add_cancel low
      obtain zero | last := _root_.String.Pos.Raw.isValid_singleton.mp tail
      · have eq : p.byteIdx = s.utf8ByteSize := by
          have diff : p.byteIdx - s.utf8ByteSize = 0 := congrArg String.Pos.Raw.byteIdx zero
          rw [diff, Nat.zero_add] at restore
          exact restore.symm
        exact Or.inl (String.Pos.Raw.ext eq ▸ s.endPos.isValid)
      · right
        apply String.Pos.Raw.ext
        change p.byteIdx - s.utf8ByteSize = c.utf8Size at last
        rw [last, Nat.add_comm] at restore
        exact restore.symm
  · rintro (inOriginal | rfl)
    · rw [← _root_.String.append_singleton]
      exact _root_.String.Pos.Raw.isValid_append.mpr (Or.inl inOriginal)
    · exact _root_.String.rawEndPos_push ▸ (s.push c).endPos.isValid

public theorem String.Pos.Raw.isValid_iff_isSome_utf8DecodeChar? :
    type_of% @_root_.String.Pos.Raw.isValid_iff_isSome_utf8DecodeChar? := by
  intro s p
  constructor
  · intro valid
    obtain atEnd | ⟨bound, first⟩ := String.Pos.Raw.isValid_iff_isUTF8FirstByte.mp valid
    · exact Or.inl atEnd
    · apply Or.inr
      obtain ⟨l, encode⟩ := s.isValidUTF8
      have atPos : firstAt s.toByteArray p.byteIdx := ⟨bound, first⟩
      rw [encode] at atPos ⊢
      obtain ⟨lt, first⟩ := atPos
      obtain ⟨a, b, rfl, off⟩ := splitAtFirst l p.byteIdx lt first
      cases b with
      | nil =>
        rw [List.append_nil, off] at lt
        exact (Nat.lt_irrefl _ lt).elim
      | cons c cs =>
        rw [List.utf8Encode_append, ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract,
          ByteArray.extract_append_eq_right off ByteArray.size_append, List.utf8DecodeChar?_utf8Encode_cons]
        rfl
  · rintro (rfl | decodes)
    · exact s.endPos.isValid
    · exact String.Pos.Raw.isValid_iff_isUTF8FirstByte.mpr (Or.inr
        ⟨ByteArray.lt_size_of_isSome_utf8DecodeChar? decodes, ByteArray.isUTF8FirstByte_of_isSome_utf8DecodeChar? decodes⟩)

public theorem ByteArray.extract_append_size_add : type_of% @_root_.ByteArray.extract_append_size_add := by
  intro a b i j
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, ByteArray.data_append, Array.toList_extract, ByteArray.data_extract,
    Array.toList_extract, Array.toList_append]
  unfold List.extract
  rw [List.drop_append, List.drop_of_length_le, List.nil_append]
  · change List.take (a.size + j - (a.size + i)) (List.drop (a.size + i - a.size) _) = _
    rw [Nat.add_sub_cancel_left, Nat.add_sub_add_left]
  · exact Nat.le_add_right _ _

public theorem String.Pos.Raw.IsValid.append_left : type_of% @_root_.String.Pos.Raw.IsValid.append_left := by
  intro t p h s
  apply String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero.mpr
  constructor
  · change s.utf8ByteSize + p.byteIdx ≤ (s ++ t).utf8ByteSize
    rw [String.utf8ByteSize_append]
    exact Nat.add_le_add_left h.le_utf8ByteSize _
  · change ((s.toByteArray ++ t.toByteArray).extract 0 (s.toByteArray.size + p.byteIdx)).IsValidUTF8
    rw [ByteArray.extract_eq_extract_append_extract s.toByteArray.size (Nat.zero_le _) (Nat.le_add_right ..),
      ByteArray.extract_append_eq_left rfl]
    have right := ByteArray.extract_append_size_add (a := s.toByteArray) (b := t.toByteArray) (i := 0) (j := p.byteIdx)
    rw [Nat.add_zero] at right
    rw [right]
    obtain ⟨a, ha⟩ := s.isValidUTF8
    obtain ⟨b, hb⟩ := h.isValidUTF8_extract_zero
    exact ⟨a ++ b, by rw [ha, hb, List.utf8Encode_append]⟩

private def appendBits (bit : Bool) : Nat → Nat → Nat
  | 0, high => high
  | n + 1, high =>
    let prev := appendBits bit n high * 2
    if bit then prev.succ else prev

private theorem incrementTrailingOnes (n high : Nat) :
    (appendBits true n high).succ = appendBits false n high.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((appendBits true n high * 2).succ).succ = appendBits false n high.succ * 2
    rw [← ih, Nat.succ_mul]
private theorem boundedBits (n x y : Nat) (h : x ≤ y) :
    appendBits false n x ≤ appendBits true n y := by
  induction n with
  | zero => exact h
  | succ n ih => exact Nat.le_trans (Nat.mul_le_mul_right 2 ih) (Nat.le_succ _)
private theorem grows (n high : Nat) : high ≤ appendBits true n high := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    apply Nat.le_trans ih
    exact Nat.le_trans (Nat.le_mul_of_pos_right _ (by decide : 0 < 2)) (Nat.le_succ _)

private theorem separateFields (n x y : Nat) (h : x < y) :
    appendBits true n x < appendBits false n y := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have bound := Nat.mul_le_mul_right 2 (Nat.succ_le_of_lt ih)
    rw [Nat.succ_mul] at bound
    exact bound

private theorem restoreWidth {w k : Nat} {x : BitVec w} (fits : x.toNat < 2 ^ k) :
    (x.setWidth k).setWidth w = x := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt x.isLt]

private theorem nextWordBound {a b : Nat} {v : UInt32} (next : a.succ = b)
    (ha : a < 2^32) (hb : b < 2^32) (lower : UInt32.ofNat a < v) : UInt32.ofNat b ≤ v :=
  (UInt32.ofNat_le_iff hb).mpr (next ▸ (UInt32.ofNat_lt_iff ha).mp lower)

open _root_.ByteArray.utf8DecodeChar? in
public theorem ByteArray.utf8DecodeChar?_utf8EncodeChar_append :
    type_of% @_root_.ByteArray.utf8DecodeChar?_utf8EncodeChar_append := by
  intro b c
  match hc : c.utf8Size, c.utf8Size_pos, c.utf8Size_le_four with
  | 1, _, _ =>
    have size : (String.utf8EncodeChar c).length = 1 := (String.length_utf8EncodeChar c).trans hc
    rw [utf8DecodeChar?_append_eq_assemble₁ size (parseFirstByte_utf8EncodeChar_eq_done hc)]
    change some _ = some c
    apply congrArg some
    apply Char.ext
    apply UInt32.toNat_inj.mp
    rw [UInt8.toNat_toUInt32]
    have bound : c.val.toNat < 256 := Nat.lt_of_le_of_lt (Char.utf8Size_eq_one_iff.mp hc) (by decide : 127 < 256)
    have head : (String.utf8EncodeChar c)[0] = c.val.toUInt8 := by
      have eq := List.eq_getElem_of_length_eq_one (String.utf8EncodeChar c) size
      exact (List.cons.inj ((String.utf8EncodeChar_eq_singleton hc).symm.trans eq)).1.symm
    rw [head, UInt32.toNat_toUInt8, Nat.mod_eq_of_lt bound]
  | 2, _, _ =>
    have size : (String.utf8EncodeChar c).length = 2 := (String.length_utf8EncodeChar c).trans hc
    rw [utf8DecodeChar?_append_eq_assemble₂ size (parseFirstByte_utf8EncodeChar_eq_oneMore hc)]
    apply assemble₂_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc
    · exact nextWordBound (a := 127) (incrementTrailingOnes 7 0) (by decide) (by decide) (Char.utf8Size_eq_two_iff.mp hc).1
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_two hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        ← BitVec.setWidth_eq_extractLsb' (by decide),
        restoreWidth]
      have upper := (UInt32.le_ofNat_iff (by decide : 2047 < 2 ^ 32)).mp (Char.utf8Size_eq_two_iff.mp hc).2
      exact (show (2047 : Nat).succ = 2^11 from incrementTrailingOnes 11 0) ▸ Nat.lt_succ_of_le upper
  | 3, _, _ =>
    have size : (String.utf8EncodeChar c).length = 3 := (String.length_utf8EncodeChar c).trans hc
    rw [utf8DecodeChar?_append_eq_assemble₃ size (parseFirstByte_utf8EncodeChar_eq_twoMore hc)]
    apply assemble₃_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc
    · exact nextWordBound (a := 2047) (incrementTrailingOnes 11 0) (by decide) (by decide) (Char.utf8Size_eq_three_iff.mp hc).1
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_three hc,
        String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_three hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        ← BitVec.setWidth_eq_extractLsb' (by decide), restoreWidth]
      have upper := (UInt32.le_ofNat_iff (by decide : 65535 < 2 ^ 32)).mp (Char.utf8Size_eq_three_iff.mp hc).2
      exact (show (65535 : Nat).succ = 2^16 from incrementTrailingOnes 16 0) ▸ Nat.lt_succ_of_le upper
  | 4, _, _ =>
    have size : (String.utf8EncodeChar c).length = 4 := (String.length_utf8EncodeChar c).trans hc
    rw [utf8DecodeChar?_append_eq_assemble₄ size (parseFirstByte_utf8EncodeChar_eq_threeMore hc)]
    apply assemble₄_eq_some_of_toBitVec
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc
    · apply isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc
    · exact nextWordBound (a := 65535) (incrementTrailingOnes 16 0) (by decide) (by decide) (Char.utf8Size_eq_four_iff.mp hc)
    · rw [String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_one_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_two_of_utf8Size_eq_four hc,
        String.toBitVec_getElem_utf8EncodeChar_three_of_utf8Size_eq_four hc,
        BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right, BitVec.setWidth_append_eq_right,
        BitVec.setWidth_append_eq_right,
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
        ← BitVec.setWidth_eq_extractLsb' (by decide), restoreWidth]
      exact Nat.lt_of_le_of_lt c.toNat_le (separateFields 16 16 32 (by decide))

private theorem encodedContinuation (x : Fin 64) :
    _root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte (UInt8.ofNat (x.val + 128)) = false := by
  have masked : UInt8.ofNat (x.val + 128) &&& 192 = 128 := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.add_lt_add_right x.isLt 128) (by decide))]
    exact highestBits (tag := 2) (mask := 192) (k := 6) x.isLt rfl
  unfold _root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte
  rw [masked]
  rfl

private def tailBytes (bytes : List UInt8) : Prop :=
  ∀ i (h : i < bytes.length), 0 < i → _root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte bytes[i] = false

private theorem tailBytes_encodeChar (c : Char) : tailBytes (String.utf8EncodeChar c) := by
  unfold String.utf8EncodeChar
  dsimp only
  split
  · intro i bound pos
    exact (Nat.not_le_of_lt pos (Nat.le_of_lt_succ bound)).elim
  · split
    · intro i bound pos
      match i, bound with
      | 0, _ => exact (Nat.lt_irrefl 0 pos).elim
      | 1, _ => exact encodedContinuation ⟨_, Nat.mod_lt _ (by decide)⟩
    · split
      · intro i bound pos
        match i, bound with
        | 0, _ => exact (Nat.lt_irrefl 0 pos).elim
        | 1, _ | 2, _ => exact encodedContinuation ⟨_, Nat.mod_lt _ (by decide)⟩
      · intro i bound pos
        match i, bound with
        | 0, _ => exact (Nat.lt_irrefl 0 pos).elim
        | 1, _ | 2, _ | 3, _ => exact encodedContinuation ⟨_, Nat.mod_lt _ (by decide)⟩

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_two) := by
  intro c size
  have bound : 1 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 1 < 2)
  exact tailBytes_encodeChar c 1 bound (by decide)

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_three) := by
  intro c size
  have bound : 1 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 1 < 3)
  exact tailBytes_encodeChar c 1 bound (by decide)

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_three) := by
  intro c size
  have bound : 2 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 2 < 3)
  exact tailBytes_encodeChar c 2 bound (by decide)

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_one_of_utf8Size_eq_four) := by
  intro c size
  have bound : 1 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 1 < 4)
  exact tailBytes_encodeChar c 1 bound (by decide)

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_two_of_utf8Size_eq_four) := by
  intro c size
  have bound : 2 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 2 < 4)
  exact tailBytes_encodeChar c 2 bound (by decide)

public theorem ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four) := by
  intro c size
  have bound : 3 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 3 < 4)
  exact tailBytes_encodeChar c 3 bound (by decide)

public theorem String.Pos.Raw.IsValid.append_right : type_of% @_root_.String.Pos.Raw.IsValid.append_right := by
  intro s p valid t
  apply String.Pos.Raw.isValid_iff_isValidUTF8_extract_zero.mpr
  constructor
  · change p.byteIdx ≤ (s ++ t).utf8ByteSize
    rw [String.utf8ByteSize_append]
    exact Nat.le_trans valid.le_utf8ByteSize (Nat.le_add_right ..)
  · have cut : (s.toByteArray ++ t.toByteArray).extract 0 p.byteIdx = s.toByteArray.extract 0 p.byteIdx := by
      apply ByteArray.ext
      apply Array.ext'
      rw [ByteArray.data_extract, ByteArray.data_append, Array.toList_extract, ByteArray.data_extract,
        Array.toList_extract, Array.toList_append]
      unfold List.extract
      rw [List.drop_zero, List.drop_zero, Nat.sub_zero, List.take_append_of_le_length]
      exact valid.le_utf8ByteSize
    exact cut ▸ valid.isValidUTF8_extract_zero

public theorem ByteArray.lt_size_of_isSome_utf8DecodeChar? : type_of% @_root_.ByteArray.lt_size_of_isSome_utf8DecodeChar? := by
  intro b i ok
  obtain ⟨c, eq⟩ := Option.isSome_iff_exists.mp ok
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.utf8Size_pos) (ByteArray.le_size_of_utf8DecodeChar?_eq_some eq)

open _root_.ByteArray.utf8DecodeChar?

public theorem ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec) := by
  intro w x hx c lower bits
  have value := UInt32.eq_of_toBitVec_eq (bits.trans toBitVec_assemble₂Unchecked.symm)
  unfold assemble₂
  rw [hx]
  split <;> try (rename_i impossible; cases impossible; done)
  dsimp only
  split
  · rename_i short
    exact (UInt32.not_lt.mpr lower (value ▸ short)).elim
  · apply congrArg some
    exact Char.ext value.symm

public theorem ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec) := by
  intro w x y hx hy c lower bits
  have value := UInt32.eq_of_toBitVec_eq (bits.trans toBitVec_assemble₃Unchecked.symm)
  unfold assemble₃
  rw [hx, hy]
  first | rw [show (false || false || false) = false from rfl] | rw [show (false || false) = false from rfl]
  split <;> try (rename_i impossible; cases impossible; done)
  dsimp only
  split
  · rename_i short
    exact (UInt32.not_lt.mpr lower (value ▸ short)).elim
  · split
    · rename_i surrogate
      rcases c.valid with below | ⟨above, _⟩
      · exact (Nat.not_le_of_gt below ((UInt32.ofNat_le_iff (by decide : 0xd800 < 2 ^ 32)).mp (value ▸ surrogate.1))).elim
      · exact (Nat.not_le_of_gt above ((UInt32.le_ofNat_iff (by decide : 0xdfff < 2 ^ 32)).mp (value ▸ surrogate.2))).elim
    · apply congrArg some
      exact Char.ext value.symm

public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec) := by
  intro w x y z hx hy hz c lower bits
  have value := UInt32.eq_of_toBitVec_eq (bits.trans toBitVec_assemble₄Unchecked.symm)
  unfold assemble₄
  rw [hx, hy, hz]
  first | rw [show (false || false || false) = false from rfl] | rw [show (false || false) = false from rfl]
  split <;> try (rename_i impossible; cases impossible; done)
  dsimp only
  split
  · rename_i short
    exact (UInt32.not_lt.mpr lower (value ▸ short)).elim
  · split
    · rename_i tooLarge
      have out : (1114111 : UInt32) < c.val := value ▸ tooLarge
      exact (Nat.not_lt_of_ge c.toNat_le ((UInt32.ofNat_lt_iff (by decide : 0x10ffff < 2 ^ 32)).mp out)).elim
    · apply congrArg some
      exact Char.ext value.symm

public theorem ByteArray.utf8DecodeChar?.helper₃ :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) := by
  intro x n hn
  apply BitVec.toNat_inj.mp
  rw [UInt32.toNat_toBitVec, UInt8.toNat_toUInt32, BitVec.toNat_setWidth, BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
  have powLt : 2 ^ n < 2 ^ 8 := Nat.pow_lt_pow_right (by decide) hn
  have maskLt : 2 ^ n - 1 < 2 ^ 8 := Nat.lt_of_le_of_lt (Nat.sub_le ..) powLt
  rw [UInt8.toNat_and, UInt8.toNat_ofNat_of_lt' maskLt, Nat.and_two_pow_sub_one_eq_mod]
  symm
  apply Nat.mod_eq_of_lt
  exact Nat.lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.lt_trans powLt (by decide : 2 ^ 8 < 2 ^ 32))

public theorem ByteArray.utf8DecodeChar?.toBitVec_assemble₂Unchecked :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_assemble₂Unchecked) := by
  intro w x
  have hw : (w &&& 31).toUInt32.toBitVec = (w.toBitVec.setWidth 5).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 5 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  rw [assemble₂Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, hw, hx]
  exact BitVec.setWidth_append_eq_shiftLeft_setWidth_or.symm

public theorem ByteArray.utf8DecodeChar?.toBitVec_assemble₃Unchecked :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_assemble₃Unchecked) := by
  intro w x y
  have hw : (w &&& 15).toUInt32.toBitVec = (w.toBitVec.setWidth 4).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 4 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  have hy : (y &&& 63).toUInt32.toBitVec = (y.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  rw [assemble₃Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft,
    hw, hx, hy, BitVec.setWidth_append_append_eq_shiftLeft_setWidth_or]
  rfl

public theorem ByteArray.utf8DecodeChar?.toBitVec_assemble₄Unchecked :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.toBitVec_assemble₄Unchecked) := by
  intro w x y z
  have hw : (w &&& 7).toUInt32.toBitVec = (w.toBitVec.setWidth 3).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 3 (by decide)
  have hx : (x &&& 63).toUInt32.toBitVec = (x.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  have hy : (y &&& 63).toUInt32.toBitVec = (y.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  have hz : (z &&& 63).toUInt32.toBitVec = (z.toBitVec.setWidth 6).setWidth 32 := (private_decl% @_root_.ByteArray.utf8DecodeChar?.helper₃) 6 (by decide)
  rw [assemble₄Unchecked, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftLeft, hw, hx, hy, hz, BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or]
  rfl

public theorem String.Pos.Raw.isValid_singleton : type_of% @_root_.String.Pos.Raw.isValid_singleton := by
  intro c p
  constructor
  · intro valid
    obtain atEnd | ⟨lt, first⟩ := String.Pos.Raw.isValid_iff_isUTF8FirstByte.mp valid
    · exact Or.inr ((congrArg String.Pos.Raw.byteIdx atEnd).trans String.utf8ByteSize_singleton)
    · apply Or.inl
      apply String.Pos.Raw.ext
      apply (List.isUTF8FirstByte_getElem_utf8Encode_singleton (c := c) (hi := lt)).mp
      exact first
  · rintro (rfl | eq)
    · exact String.Pos.Raw.isValid_zero
    · have atEnd : p = (String.singleton c).rawEndPos :=
        String.Pos.Raw.ext (eq.trans String.utf8ByteSize_singleton.symm)
      exact atEnd ▸ String.Pos.Raw.isValid_rawEndPos

private theorem firstOfTag (w : UInt8) (valid : parseFirstByte w ≠ .invalid) : w.IsUTF8FirstByte := by
  unfold parseFirstByte at valid
  split at valid <;> rename_i h₁
  · exact Or.inl (eq_of_beq h₁)
  · split at valid <;> rename_i h₂
    · exact Or.inr (Or.inl (eq_of_beq h₂))
    · split at valid <;> rename_i h₃
      · exact Or.inr (Or.inr (Or.inl (eq_of_beq h₃)))
      · split at valid <;> rename_i h₄
        · exact Or.inr (Or.inr (Or.inr (eq_of_beq h₄)))
        · exact (valid rfl).elim

public theorem ByteArray.isUTF8FirstByte_of_isSome_utf8DecodeChar? :
    type_of% @_root_.ByteArray.isUTF8FirstByte_of_isSome_utf8DecodeChar? := by
  intro b i ok
  apply firstOfTag
  intro invalid
  have lt : i < b.size := ByteArray.lt_size_of_isSome_utf8DecodeChar? ok
  unfold ByteArray.utf8DecodeChar? at ok
  rw [dite_eq_left lt] at ok
  split at ok
  · cases ok
  all_goals rename_i tag
  all_goals cases tag.symm.trans invalid

public theorem Nat.mod_two_pow_shiftLeft_mod_two_pow : type_of% @_root_.Nat.mod_two_pow_shiftLeft_mod_two_pow := by
  intro a b c
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mod_mul_mod]

public theorem BitVec.setWidth_append_eq_shiftLeft_setWidth_or :
    type_of% @_root_.BitVec.setWidth_append_eq_shiftLeft_setWidth_or := by
  intro w v k b c
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_append, Nat.or_mod_two_pow, Nat.mod_two_pow_shiftLeft_mod_two_pow]

public theorem BitVec.shiftLeft_or_distrib : type_of% @_root_.BitVec.shiftLeft_or_distrib := by
  intro w a b s
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_or,
    BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, Nat.shiftLeft_or_distrib, Nat.or_mod_two_pow]

public theorem BitVec.shiftLeft_add : type_of% @_root_.BitVec.shiftLeft_add := by
  intro w b s t
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft,
    Nat.mod_two_pow_shiftLeft_mod_two_pow, Nat.shiftLeft_add]

public theorem Nat.shiftLeft_or_distrib : type_of% @_root_.Nat.shiftLeft_or_distrib := by
  intro i a b
  have parts := Nat.mod_add_div (2^i * a ||| 2^i * b) (2^i)
  rw [Nat.or_mod_two_pow, Nat.or_div_two_pow, Nat.mul_mod_right, Nat.mul_mod_right,
    Nat.zero_or, Nat.zero_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)] at parts
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_comm _ (2^i), Nat.mul_comm a, Nat.mul_comm b]
  exact parts

public theorem Char.toNat_le : type_of% (private_decl% @_root_.Char.toNat_le) := by
  intro c
  rcases c.valid with below | ⟨_, upper⟩
  · exact Nat.le_trans (Nat.le_of_lt below) (boundedBits 11 27 543 (Nat.le_trans (by decide : 27 ≤ 33) (grows 4 33)))
  · have carry : (0x10ffff : Nat).succ = 0x110000 := incrementTrailingOnes 16 16
    exact Nat.le_of_lt_succ (carry.symm ▸ upper)

public theorem BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' : type_of% @_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' := by
  intro w s₂ s₁ l₁ l₂ x eq
  subst s₂
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_comm _ (2 ^ l₁)]
  rw [← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos l₁)), Nat.add_comm,
    Nat.pow_add 2 s₁, ← Nat.div_div_eq_div_mul, Nat.add_comm l₂ l₁, Nat.pow_add, Nat.mod_mul]
public theorem BitVec.setWidth_append_eq_right : type_of% @_root_.BitVec.setWidth_append_eq_right := by
  intro w v a b
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.or_mod_two_pow,
    Nat.shiftLeft_eq, Nat.mul_mod_left, Nat.zero_or, Nat.mod_eq_of_lt b.isLt]
public theorem BitVec.setWidth_eq_extractLsb' : type_of% @_root_.BitVec.setWidth_eq_extractLsb' := by
  intro v x w h
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

private theorem maskFromFields {b : UInt8} {w k : Nat} {tag : BitVec w} {field : BitVec k}
    (size : w + k = 8) (fields : b.toBitVec = (tag ++ field).cast size)
    (mask value : UInt8) (zero : mask.toNat % 2^k = 0)
    (result : 2 ^ k * (tag.toNat &&& (mask.toNat / 2^k)) = value.toNat) : b &&& mask = value := by
  have parts := congrArg BitVec.toNat fields
  rw [UInt8.toNat_toBitVec, BitVec.toNat_cast, BitVec.toNat_append, Nat.shiftLeft_eq,
    Nat.mul_comm tag.toNat, ← Nat.two_pow_add_eq_or_of_lt field.isLt, Nat.add_comm] at parts
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and, parts]
  exact (highestBits field.isLt zero).trans result

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_done :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_done) := by
  intro c size
  have bound : 0 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 0 < 1)
  let b := (String.utf8EncodeChar c)[0]'bound
  have fields : b.toBitVec = 0#1 ++ c.val.toBitVec.extractLsb' 0 7 := (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one) size
  change parseFirstByte b = _
  unfold parseFirstByte
  rw [maskFromFields (tag := 0#1) (k := 7) rfl fields 128 0 rfl rfl]
  rfl

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_oneMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_oneMore) := by
  intro c size
  have bound : 0 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 0 < 2)
  let b := (String.utf8EncodeChar c)[0]'bound
  have fields : b.toBitVec = 6#3 ++ c.val.toBitVec.extractLsb' 6 5 := (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_two) size
  change parseFirstByte b = _
  unfold parseFirstByte
  rw [maskFromFields (tag := 6#3) (k := 5) rfl fields 128 128 rfl rfl]
  rw [maskFromFields (tag := 6#3) (k := 5) rfl fields 224 192 rfl rfl]
  rfl

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_twoMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_twoMore) := by
  intro c size
  have bound : 0 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 0 < 3)
  let b := (String.utf8EncodeChar c)[0]'bound
  have fields : b.toBitVec = 14#4 ++ c.val.toBitVec.extractLsb' 12 4 := (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_three) size
  change parseFirstByte b = _
  unfold parseFirstByte
  rw [maskFromFields (tag := 14#4) (k := 4) rfl fields 128 128 rfl rfl]
  rw [maskFromFields (tag := 14#4) (k := 4) rfl fields 224 224 rfl rfl]
  rw [maskFromFields (tag := 14#4) (k := 4) rfl fields 240 224 rfl rfl]
  rfl

public theorem ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_threeMore :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_threeMore) := by
  intro c size
  have bound : 0 < (String.utf8EncodeChar c).length := (String.length_utf8EncodeChar c).trans size ▸ (by decide : 0 < 4)
  let b := (String.utf8EncodeChar c)[0]'bound
  have fields : b.toBitVec = 30#5 ++ c.val.toBitVec.extractLsb' 18 3 := (private_decl% @_root_.String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_four) size
  change parseFirstByte b = _
  unfold parseFirstByte
  rw [maskFromFields (tag := 30#5) (k := 3) rfl fields 128 128 rfl rfl]
  rw [maskFromFields (tag := 30#5) (k := 3) rfl fields 224 224 rfl rfl]
  rw [maskFromFields (tag := 30#5) (k := 3) rfl fields 240 240 rfl rfl]
  rw [maskFromFields (tag := 30#5) (k := 3) rfl fields 248 240 rfl rfl]
  rfl

public theorem BitVec.extractLsb'_append_eq_right : type_of% @_root_.BitVec.extractLsb'_append_eq_right := by
  intro w v a b
  rw [← BitVec.setWidth_eq_extractLsb' (Nat.le_add_left v w), BitVec.setWidth_append_eq_right]

public theorem BitVec.append_assoc : type_of% @_root_.BitVec.append_assoc := by
  intro w v k a b c
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    BitVec.toNat_append, Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add, Nat.or_assoc]


public theorem ByteArray.extract_append_size_left : type_of% @_root_.ByteArray.extract_append_size_left := by
  intro a b i
  have segment : (a ++ b).extract 0 a.size = a := ByteArray.extract_append_eq_left rfl
  have both := congrArg (fun x : ByteArray => x.extract i a.size) segment
  rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_self] at both
  exact both
public theorem ByteArray.utf8DecodeChar?_append_eq_some : type_of% @_root_.ByteArray.utf8DecodeChar?_append_eq_some := by
  intro b i c success t
  have inside : i ≤ b.size := Nat.le_of_lt (ByteArray.lt_size_of_isSome_utf8DecodeChar? (success ▸ rfl))
  have extend : b.size ≤ (b ++ t).size := ByteArray.size_append.symm ▸ Nat.le_add_right b.size t.size
  rw [ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract] at ⊢ success
  rw [ByteArray.extract_eq_extract_append_extract b.size inside extend, ByteArray.extract_append_size_left,
    ByteArray.eq_of_utf8DecodeChar?_eq_some success, ByteArray.append_assoc, ByteArray.utf8DecodeChar?_utf8EncodeChar_append]

public theorem ByteArray.utf8DecodeChar_extract_congr_of_le : type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar_extract_congr_of_le) := by
  intro bytes i j k valid₁ valid₂ order
  obtain ⟨c, first⟩ := Option.isSome_iff_exists.mp valid₁
  have nonempty := ByteArray.lt_size_of_isSome_utf8DecodeChar? valid₁
  rw [ByteArray.size_extract] at nonempty
  have ij := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_sub_pos nonempty) (Nat.min_le_left ..))
  have second := ByteArray.utf8DecodeChar?_append_eq_some first (bytes.extract j k)
  rw [← ByteArray.extract_eq_extract_append_extract j ij order] at second
  exact (Option.get_of_eq_some valid₁ first).trans (Option.get_of_eq_some valid₂ second).symm

public theorem ByteArray.utf8DecodeChar?.assemble₂._proof_1 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₂._proof_1) :=
  fun _ _ high impossible => impossible (Nat.lt_trans
    (Nat.mul_lt_mul_of_pos_right high (by decide : 0 < 2 ^ 6)) (by decide : 2048 < 4294967296))

public theorem ByteArray.utf8DecodeChar?.assemble₂._proof_2 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₂._proof_2) :=
  fun _ _ high low impossible => impossible (Nat.lt_trans
    (Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left high (by decide : 0 < 2 ^ 6)) low)
    (by decide : 2112 < 55296))

public theorem ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec._proof_1_8 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec._proof_1_8) :=
  fun bounds => bounds.2.elim (Nat.not_lt_of_ge bounds.1.1)
    (fun hi => Nat.not_lt_of_ge bounds.1.2 hi.1)

public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq._proof_1_13 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_iff_utf8EncodeChar_eq._proof_1_13) :=
  fun bound impossible => impossible (Nat.lt_of_le_of_lt bound (by decide : 1114111 < 2097152))

public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec._proof_1_2 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec._proof_1_2) :=
  fun bounds => Nat.not_lt_of_ge bounds.1 bounds.2

public theorem ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec._proof_1_8 :
    type_of% (private_decl% @_root_.ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec._proof_1_8) :=
  fun bounds => bounds.2.elim
    (fun lo => Nat.not_lt_of_ge (Nat.le_of_lt bounds.1) (Nat.lt_trans lo (by decide : 55296 < 1114111)))
    (fun hi => Nat.not_lt_of_ge bounds.1 hi.2)

public theorem Char.toNat_le._proof_1_1 :
    type_of% (private_decl% @_root_.Char.toNat_le._proof_1_1) :=
  fun ranges impossible => ranges.elim
    (fun lower => impossible (Nat.le_trans (Nat.le_of_lt lower) (by decide : 55296 ≤ 1114111)))
    (fun upper => impossible (Nat.le_of_lt_succ upper.2))

public theorem Char.utf8Size_eq_four_iff._proof_1_4 :
    type_of% (private_decl% @_root_.Char.utf8Size_eq_four_iff._proof_1_4) :=
  fun bound impossible => impossible (Nat.le_trans bound (by decide : 127 ≤ 65535))

public theorem Char.utf8Size_eq_four_iff._proof_1_5 :
    type_of% (private_decl% @_root_.Char.utf8Size_eq_four_iff._proof_1_5) :=
  fun _ bound impossible => impossible (Nat.le_trans bound (by decide : 2047 ≤ 65535))

public theorem String.utf8EncodeChar_eq_utf8EncodeCharFast._proof_1_12 :
    type_of% (private_decl% @_root_.String.utf8EncodeChar_eq_utf8EncodeCharFast._proof_1_12) :=
  fun _ _ bound impossible => impossible ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 12)).mpr
    (Nat.lt_of_le_of_lt bound (by decide : 65535 < 256 * 2 ^ 12)))

end OmegaChecks.InitPort.Alternatives
