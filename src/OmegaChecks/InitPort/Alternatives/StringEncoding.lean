module
import all Init.Data.String.Decode
import all Init.Data.String.Basic
import all Init.Data.ByteArray.Lemmas

/-! The leading and continuation byte ranges of UTF-8 code points. -/

namespace OmegaChecks.InitPort.Alternatives

private def checkBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => checkBelow p n && p n

private theorem checkedBelow {p : Nat → Bool} {n : Nat} (check : checkBelow p n = true) :
    ∀ x : Fin n, p x.val = true := by
  induction n with
  | zero => intro x; exact (Nat.not_lt_zero x.val x.isLt).elim
  | succ n ih =>
    intro x
    have both := Bool.and_eq_true_iff.mp check
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ x.isLt) with
    | inl eq => exact (congrArg p eq).trans both.2
    | inr lt => exact ih both.1 ⟨x.val, lt⟩

private theorem firstAscii (x : Fin 128) : (UInt8.ofNat x.val).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat i).IsUTF8FirstByte)) (by rfl) x)

private theorem firstTwo (x : Fin 32) : (UInt8.ofNat (x.val + 192)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 192)).IsUTF8FirstByte)) (by rfl) x)

private theorem firstThree (x : Fin 16) : (UInt8.ofNat (x.val + 224)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 224)).IsUTF8FirstByte)) (by rfl) x)

private theorem firstFour (x : Fin 8) : (UInt8.ofNat (x.val + 240)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide ((UInt8.ofNat (i + 240)).IsUTF8FirstByte)) (by rfl) x)

private theorem continuation (x : Fin 64) : ¬ (UInt8.ofNat (x.val + 128)).IsUTF8FirstByte :=
  of_decide_eq_true (checkedBelow (p := fun i => decide (¬ (UInt8.ofNat (i + 128)).IsUTF8FirstByte)) (by rfl) x)

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

public theorem String.Pos.Raw.isValid_iff_isUTF8FirstByte :
    type_of% @_root_.String.Pos.Raw.isValid_iff_isUTF8FirstByte := by
  intro s p
  constructor
  · intro valid
    by_cases eq : p = s.rawEndPos
    · exact Or.inl eq
    · have lt := Nat.lt_of_le_of_ne valid.le_utf8ByteSize (fun h => eq (String.Pos.Raw.ext h))
      have suffix := valid.isValidUTF8_extract_utf8ByteSize
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
