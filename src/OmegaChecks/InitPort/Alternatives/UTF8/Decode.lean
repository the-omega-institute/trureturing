module

public import Init.Data.String.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Basic

namespace OmegaChecks.InitPort.Alternatives

private theorem done_byte_lt (w : UInt8) (h : ByteArray.utf8DecodeChar?.parseFirstByte w = .done) :
    w.toNat < 128 := by
  have zero : w &&& 128 = 0 := by
    unfold ByteArray.utf8DecodeChar?.parseFirstByte at h
    split at h
    · exact of_decide_eq_true (by assumption)
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h <;> cases h
  by_cases hi : 128 ≤ w.toNat
  · have bit := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (i := 7) hi w.toNat_lt_size
    have eq := congrArg (fun b : UInt8 => b.toNat.testBit 7) zero
    change (w &&& 128).toNat.testBit 7 = (0 : UInt8).toNat.testBit 7 at eq
    rw [UInt8.toNat_and, Nat.testBit_and, bit] at eq
    exact Bool.noConfusion eq
  · exact Nat.lt_of_not_ge hi

private theorem masked_shift_lt (b : UInt8) (mask : UInt8) (width shift : Nat)
    (hm : mask.toNat < 2 ^ width) (hs : shift < 32) :
    ((b &&& mask).toUInt32 <<< UInt32.ofNat shift).toNat < 2 ^ (width + shift) := by
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat_of_lt' (Nat.lt_trans hs (by decide : 32 < 2 ^ 32)),
    Nat.mod_eq_of_lt hs, UInt8.toNat_toUInt32, UInt8.toNat_and, Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le ..)
    (Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow _ hm) (Nat.two_pow_pos _))

private theorem second_byte_bound (w x : UInt8) :
    (ByteArray.utf8DecodeChar?.assemble₂Unchecked w x).toNat < 2 ^ 11 := by
  rw [ByteArray.utf8DecodeChar?.assemble₂Unchecked, UInt32.toNat_or, UInt8.toNat_toUInt32]
  exact Nat.or_lt_two_pow (masked_shift_lt w 31 5 6 (by decide) (by decide))
    (Nat.lt_of_lt_of_le (UInt8.toNat_lt_size _)
      (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 8 ≤ 11)))

private theorem third_byte_bound (w x y : UInt8) :
    (ByteArray.utf8DecodeChar?.assemble₃Unchecked w x y).toNat < 2 ^ 16 := by
  rw [ByteArray.utf8DecodeChar?.assemble₃Unchecked, UInt32.toNat_or, UInt32.toNat_or, UInt8.toNat_toUInt32]
  apply Nat.or_lt_two_pow
  · exact Nat.or_lt_two_pow (masked_shift_lt w 15 4 12 (by decide) (by decide))
      (Nat.lt_of_lt_of_le (masked_shift_lt x 63 6 6 (by decide) (by decide))
        (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 12 ≤ 16)))
  · exact Nat.lt_of_lt_of_le (UInt8.toNat_lt_size _)
      (Nat.pow_le_pow_right (Nat.zero_lt_succ 1) (by decide : 8 ≤ 16))

public theorem ByteArray.utf8DecodeChar?.utf8Size_assemble₁ :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.utf8Size_assemble₁) := by
  intro w c h hc
  cases Option.some.inj hc
  apply Char.utf8Size_eq_one_iff.2
  apply (UInt32.le_ofNat_iff (by decide : 127 < 2 ^ 32)).2
  exact Nat.le_of_lt_succ (done_byte_lt w h)

public theorem ByteArray.utf8DecodeChar?.val_assemble₂_le :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.val_assemble₂_le) := by
  intro w x c
  fun_cases _root_.ByteArray.utf8DecodeChar?.assemble₂ w x with
  | case1 => intro h; cases h
  | case2 => intro h; cases h
  | case3 =>
    intro h
    cases Option.some.inj h
    exact (UInt32.le_ofNat_iff (by decide : 2047 < 2 ^ 32)).2 (Nat.le_of_lt_succ (second_byte_bound w x))

private def lowMask (n : Nat) : Nat := Nat.rec 0 (fun _ r => (r * 2).succ) n

private theorem succ_lowMask (n : Nat) : (lowMask n).succ = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, ← ih, Nat.succ_mul]; rfl

public theorem ByteArray.utf8DecodeChar?.val_assemble₃_le :
    type_of% (private_decl% @ByteArray.utf8DecodeChar?.val_assemble₃_le) := by
  intro w x y c
  fun_cases _root_.ByteArray.utf8DecodeChar?.assemble₃ w x y with
  | case1 => intro h; cases h
  | case2 => intro h; cases h
  | case3 => intro h; cases h
  | case4 =>
    intro h
    cases Option.some.inj h
    apply (UInt32.le_ofNat_iff (by decide : 65535 < 2 ^ 32)).2
    apply Nat.le_of_lt_succ (n := lowMask 16)
    rw [succ_lowMask]
    exact third_byte_bound w x y

private theorem size_le_two (c : Char) (hi : c.val ≤ 2047) : c.utf8Size ≤ 2 := by
  dsimp only [Char.utf8Size]
  split
  · decide
  · rw [ite_eq_left ((UInt32.le_iff_toNat_le).2 (UInt32.toNat_ofNatLT.symm ▸
      (UInt32.le_ofNat_iff (by decide : 2047 < 2 ^ 32)).1 hi))]
    exact Nat.le_refl _

private theorem size_le_three (c : Char) (hi : c.val ≤ 65535) : c.utf8Size ≤ 3 := by
  dsimp only [Char.utf8Size]
  split
  · decide
  · split
    · decide
    · rw [ite_eq_left ((UInt32.le_iff_toNat_le).2 (UInt32.toNat_ofNatLT.symm ▸
        (UInt32.le_ofNat_iff (by decide : 65535 < 2 ^ 32)).1 hi))]
      exact Nat.le_refl _

public theorem ByteArray.le_size_of_utf8DecodeChar?_eq_some :
    type_of% @_root_.ByteArray.le_size_of_utf8DecodeChar?_eq_some := by
  intro b i c
  fun_cases b.utf8DecodeChar? i with
  | case1 => intro h; cases h
  | case2 =>
    intro h
    rw [(private_decl% _root_.ByteArray.utf8DecodeChar?.utf8Size_assemble₁) h]
    assumption
  | case3 =>
    intro h
    exact Nat.le_trans (Nat.add_le_add_left (size_le_two c ((private_decl% _root_.ByteArray.utf8DecodeChar?.val_assemble₂_le) h)) i) (by assumption)
  | case4 => intro h; cases h
  | case5 =>
    intro h
    exact Nat.le_trans (Nat.add_le_add_left (size_le_three c ((private_decl% _root_.ByteArray.utf8DecodeChar?.val_assemble₃_le) h)) i) (by assumption)
  | case6 => intro h; cases h
  | case7 =>
    intro _
    exact Nat.le_trans (Nat.add_le_add_left c.utf8Size_le_four i) (by assumption)
  | case8 => intro h; cases h
  | case9 => intro h; cases h

private def firstWidth : List UInt8 → Nat
  | [] => 0
  | b :: _ => if b.toNat < 128 then 1 else if b.toNat < 224 then 2 else if b.toNat < 240 then 3 else 4

private theorem width_two {v : Nat} (bs : List UInt8) :
    firstWidth (UInt8.ofNat (v % 32 + 192) :: bs) = 2 := by
  have upper := Nat.add_lt_add_right (Nat.mod_lt v (by decide : 0 < 32)) 192
  have lower : 192 ≤ v % 32 + 192 := Nat.le_add_left ..
  dsimp only [firstWidth]
  rw [UInt8.toNat_ofNat_of_lt' (Nat.lt_trans upper (by decide : 224 < 256)),
    ite_eq_right (Nat.not_lt_of_ge (Nat.le_trans (by decide : 128 ≤ 192) lower)), ite_eq_left upper]
private theorem width_three {v : Nat} (bs : List UInt8) :
    firstWidth (UInt8.ofNat (v % 16 + 224) :: bs) = 3 := by
  have upper := Nat.add_lt_add_right (Nat.mod_lt v (by decide : 0 < 16)) 224
  have lower : 224 ≤ v % 16 + 224 := Nat.le_add_left ..
  dsimp only [firstWidth]
  rw [UInt8.toNat_ofNat_of_lt' (Nat.lt_trans upper (by decide : 240 < 256)),
    ite_eq_right (Nat.not_lt_of_ge (Nat.le_trans (by decide : 128 ≤ 224) lower)),
    ite_eq_right (Nat.not_lt_of_ge lower), ite_eq_left upper]
private theorem width_four {v : Nat} (bs : List UInt8) :
    firstWidth (UInt8.ofNat (v % 8 + 240) :: bs) = 4 := by
  have upper := Nat.add_lt_add_right (Nat.mod_lt v (by decide : 0 < 8)) 240
  have lower : 240 ≤ v % 8 + 240 := Nat.le_add_left ..
  dsimp only [firstWidth]
  rw [UInt8.toNat_ofNat_of_lt' (Nat.lt_trans upper (by decide : 248 < 256)),
    ite_eq_right (Nat.not_lt_of_ge (Nat.le_trans (by decide : 128 ≤ 240) lower)),
    ite_eq_right (Nat.not_lt_of_ge (Nat.le_trans (by decide : 224 ≤ 240) lower)),
    ite_eq_right (Nat.not_lt_of_ge lower)]

private theorem width_encode (c : Char) (bs : List UInt8) :
    firstWidth (String.utf8EncodeChar c ++ bs) = (String.utf8EncodeChar c).length := by
  dsimp only [String.utf8EncodeChar]
  split
  · rename_i h
    dsimp only [List.cons_append, List.nil_append, firstWidth]
    rw [UInt8.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h (by decide : 127 < 256)), ite_eq_left (Nat.lt_succ_of_le h)]
    rfl
  · split
    · exact width_two _
    · split
      · exact width_three _
      · exact width_four _

private def bytes (a : ByteArray) := a.data.toList

private theorem bytes_append (a b : ByteArray) : bytes (a ++ b) = bytes a ++ bytes b := by
  unfold bytes
  rw [ByteArray.data_append, Array.toList_append]

private theorem bytes_singleton (c : Char) : bytes [c].utf8Encode = String.utf8EncodeChar c := by
  rw [List.utf8Encode_singleton]
  unfold bytes
  rw [List.data_toByteArray, List.toList_toArray]

private theorem remove_prefix (l m : List Char) (tail : List UInt8)
    (eq : bytes l.utf8Encode ++ tail = bytes m.utf8Encode) : ∃ t : List Char, tail = bytes t.utf8Encode := by
  induction l generalizing m tail with
  | nil => exact ⟨m, eq⟩
  | cons c l ih =>
    rw [List.utf8Encode_cons, bytes_append, bytes_singleton, List.append_assoc] at eq
    cases m with
    | nil =>
      have nilByte : bytes ([] : List Char).utf8Encode = [] := rfl
      rw [nilByte] at eq
      have hn : String.utf8EncodeChar c ≠ [] := by
        dsimp only [String.utf8EncodeChar]
        split
        · intro h; cases h
        · split
          · intro h; cases h
          · split <;> intro h <;> cases h
      have e : (String.utf8EncodeChar c).length = 0 := (width_encode c _).symm.trans (congrArg firstWidth eq)
      exact False.elim (hn (List.eq_nil_of_length_eq_zero e))
    | cons d m =>
      rw [List.utf8Encode_cons, bytes_append, bytes_singleton] at eq
      have same : (String.utf8EncodeChar c).length = (String.utf8EncodeChar d).length :=
        (width_encode c _).symm.trans ((congrArg firstWidth eq).trans (width_encode d _))
      have cut := congrArg (List.drop (String.utf8EncodeChar c).length) eq
      rw [List.drop_left, same, List.drop_left] at cut
      exact ih m _ cut


private theorem bytes_extract (b : ByteArray) (i j : Nat) :
    bytes (b.extract i j) = ((bytes b).drop i).take (j - i) := by
  unfold bytes
  rw [ByteArray.data_extract, Array.toList_extract]

private theorem join_slices (l : List UInt8) {i j : Nat} (h : i ≤ j) :
    l.take i ++ (l.drop i).take (j - i) = l.take j := by
  rw [List.take_drop, Nat.add_sub_of_le h]
  have start : (l.take j).take i = l.take i := List.take_take.trans (congrArg (fun n => l.take n) (Nat.min_eq_left h))
  rw [← start, List.take_append_drop]

public theorem String.Pos.isValidUTF8_extract : type_of% @_root_.String.Pos.isValidUTF8_extract := by
  intro s a b
  by_cases h : a.offset.byteIdx ≤ b.offset.byteIdx
  · obtain ⟨l, hl⟩ := a.isValid.isValidUTF8_extract_zero
    obtain ⟨m, hm⟩ := b.isValid.isValidUTF8_extract_zero
    have start := congrArg bytes hl
    have stop := congrArg bytes hm
    rw [bytes_extract, List.drop_zero, Nat.sub_zero] at start stop
    have split := join_slices (bytes s.toByteArray) h
    rw [start, stop] at split
    obtain ⟨t, ht⟩ := remove_prefix l m _ split
    exact ⟨t, ByteArray.ext (Array.ext' ((bytes_extract ..).trans ht))⟩
  · rw [ByteArray.extract_eq_empty_iff.2 (Nat.le_trans (Nat.min_le_left ..) (Nat.le_of_not_le h))]
    exact ByteArray.isValidUTF8_empty

private theorem same_decode (a b : ByteArray) (i j : Nat)
    (bound : ∀ k, i + k < a.size ↔ j + k < b.size)
    (byte : ∀ k (hi : i + k < a.size) (hj : j + k < b.size), a[i + k] = b[j + k]) :
    a.utf8DecodeChar? i = b.utf8DecodeChar? j := by
  unfold ByteArray.utf8DecodeChar?
  by_cases hi : i < a.size
  · have hj : j < b.size := (bound 0).1 hi
    rw [dite_eq_left hi, dite_eq_left hj]
    have hx := byte 0 hi hj
    change a[i] = b[j] at hx
    generalize ha : a[i] = w
    have hb : b[j] = w := hx.symm.trans ha
    rw [hb]
    split
    · rfl
    · rfl
    · by_cases h₁ : i + 1 < a.size
      · rw [dite_eq_left h₁, dite_eq_left ((bound 1).1 h₁), byte 1 h₁ ((bound 1).1 h₁)]
      · rw [dite_eq_right h₁, dite_eq_right (fun h => h₁ ((bound 1).2 h))]
    · by_cases h₂ : i + 2 < a.size
      · have hi₁ := Nat.lt_of_succ_lt h₂
        have hj₂ := (bound 2).1 h₂
        rw [dite_eq_left h₂, dite_eq_left hj₂, byte 1 hi₁ ((bound 1).1 hi₁), byte 2 h₂ hj₂]
      · rw [dite_eq_right h₂, dite_eq_right (fun h => h₂ ((bound 2).2 h))]
    · by_cases h₃ : i + 3 < a.size
      · have hi₂ := Nat.lt_of_succ_lt h₃
        have hi₁ := Nat.lt_of_succ_lt hi₂
        have hj₃ := (bound 3).1 h₃
        rw [dite_eq_left h₃, dite_eq_left hj₃, byte 1 hi₁ ((bound 1).1 hi₁),
          byte 2 hi₂ ((bound 2).1 hi₂), byte 3 h₃ hj₃]
      · rw [dite_eq_right h₃, dite_eq_right (fun h => h₃ ((bound 3).2 h))]
  · have hj : ¬j < b.size := fun h => hi ((bound 0).2 h)
    rw [dite_eq_right hi, dite_eq_right hj]

public theorem ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract :
    type_of% @_root_.ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract := by
  intro b i
  apply same_decode
  · intro k
    rw [ByteArray.size_extract, Nat.min_self, Nat.zero_add, Nat.add_comm]
    exact Nat.lt_sub_iff_add_lt.symm
  · intro k left right
    have h : (b.extract i b.size)[0 + k]'right = b[i + (0 + k)] :=
      ByteArray.getElem_extract right
    simpa only [Nat.zero_add] using h.symm


private theorem width_value (c : Char) :
    c.utf8Size = if c.val.toNat ≤ 127 then 1 else if c.val.toNat ≤ 2047 then 2 else
      if c.val.toNat ≤ 65535 then 3 else 4 := by
  dsimp only [Char.utf8Size]
  rfl

public theorem Char.utf8Size_eq_two_iff : type_of% @_root_.Char.utf8Size_eq_two_iff := by
  intro c
  rw [width_value]
  have bounds : (127 < c.val ∧ c.val ≤ 2047) ↔ (127 < c.val.toNat ∧ c.val.toNat ≤ 2047) :=
    and_congr (UInt32.ofNat_lt_iff (by decide : 127 < 2 ^ 32)) (UInt32.le_ofNat_iff (by decide : 2047 < 2 ^ 32))
  apply Iff.trans _ bounds.symm
  split
  · rename_i lo
    exact ⟨(fun h => nomatch h), fun h => False.elim (Nat.not_lt_of_ge lo h.1)⟩
  · rename_i lo
    split
    · rename_i hi
      exact ⟨fun _ => ⟨Nat.lt_of_not_ge lo, hi⟩, fun _ => rfl⟩
    · rename_i hi
      split <;> exact ⟨(fun h => nomatch h), fun h => False.elim (hi h.2)⟩

public theorem Char.utf8Size_eq_three_iff : type_of% @_root_.Char.utf8Size_eq_three_iff := by
  intro c
  rw [width_value]
  have bounds : (2047 < c.val ∧ c.val ≤ 65535) ↔ (2047 < c.val.toNat ∧ c.val.toNat ≤ 65535) :=
    and_congr (UInt32.ofNat_lt_iff (by decide : 2047 < 2 ^ 32)) (UInt32.le_ofNat_iff (by decide : 65535 < 2 ^ 32))
  apply Iff.trans _ bounds.symm
  split
  · rename_i lo
    exact ⟨(fun h => nomatch h), fun h => False.elim
      (Nat.not_lt_of_ge (Nat.le_trans lo (by decide : 127 ≤ 2047)) h.1)⟩
  · split
    · rename_i lo
      exact ⟨(fun h => nomatch h), fun h => False.elim (Nat.not_lt_of_ge lo h.1)⟩
    · rename_i lo
      split
      · rename_i hi
        exact ⟨fun _ => ⟨Nat.lt_of_not_ge lo, hi⟩, fun _ => rfl⟩
      · rename_i hi
        exact ⟨(fun h => nomatch h), fun h => False.elim (hi h.2)⟩

public theorem Char.utf8Size_eq_four_iff : type_of% @_root_.Char.utf8Size_eq_four_iff := by
  intro c
  rw [width_value]
  apply Iff.trans _ (UInt32.ofNat_lt_iff (by decide : 65535 < 2 ^ 32)).symm
  split
  · rename_i lo
    exact ⟨(fun h => nomatch h), fun h => False.elim
      (Nat.not_lt_of_ge (Nat.le_trans lo (by decide : 127 ≤ 65535)) h)⟩
  · split
    · rename_i lo
      exact ⟨(fun h => nomatch h), fun h => False.elim
        (Nat.not_lt_of_ge (Nat.le_trans lo (by decide : 2047 ≤ 65535)) h)⟩
    · split
      · rename_i lo
        exact ⟨(fun h => nomatch h), fun h => False.elim (Nat.not_lt_of_ge lo h)⟩
      · rename_i lo
        exact ⟨fun _ => Nat.lt_of_not_ge lo, fun _ => rfl⟩


private theorem size_from (b : ByteArray) (i : Nat) : (b.extract i b.size).size = b.size - i :=
  ByteArray.size_extract.trans (congrArg (· - i) (Nat.min_self _))

private theorem shift_from (b : ByteArray) (i n : Nat) (hi : i ≤ b.size) :
    (b.extract i b.size).extract n (b.extract i b.size).size = b.extract (i + n) b.size := by
  rw [ByteArray.extract_extract, size_from, Nat.add_sub_of_le hi, Nat.min_self]

private theorem same_suffix_bound {a b : ByteArray} {i j : Nat} (suffix : a.extract i a.size = b.extract j b.size) :
    i < a.size ↔ j < b.size := by
  have sizes : a.size - i = b.size - j := (size_from a i).symm.trans ((congrArg ByteArray.size suffix).trans (size_from b j))
  exact (Nat.sub_pos_iff_lt.symm.trans (by rw [sizes])).trans Nat.sub_pos_iff_lt

private theorem decode_same_suffix (fuel : Nat) {a b : ByteArray} (i j : Nat) (hi : i ≤ a.size) (hj : j ≤ b.size)
    (front acc : Array Char) (room : a.size - i ≤ fuel) (suffix : a.extract i a.size = b.extract j b.size) :
    ByteArray.utf8Decode?.go a i (front ++ acc) hi = (ByteArray.utf8Decode?.go b j acc hj).map (front ++ ·) := by
  induction fuel generalizing i j acc with
  | zero =>
    have endA := Nat.le_of_sub_eq_zero (Nat.le_zero.mp room)
    rw [ByteArray.utf8Decode?.go.eq_1 a, ByteArray.utf8Decode?.go.eq_1 b,
        ite_eq_right (Nat.not_lt_of_ge endA), ite_eq_right (fun h => Nat.not_lt_of_ge endA ((same_suffix_bound suffix).2 h))]
    rfl
  | succ n ih =>
    rw [ByteArray.utf8Decode?.go.eq_1 a, ByteArray.utf8Decode?.go.eq_1 b]
    by_cases ha : i < a.size
    · rw [ite_eq_left ha, ite_eq_left ((same_suffix_bound suffix).1 ha)]
      have code : a.utf8DecodeChar? i = b.utf8DecodeChar? j :=
        _root_.ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract.trans
          ((congrArg (fun r : ByteArray => r.utf8DecodeChar? 0) suffix).trans
            _root_.ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract.symm)
      split <;> rename_i left
      · split <;> rename_i right
        · rfl
        · cases left.symm.trans (code.trans right)
      · rename_i c
        split <;> rename_i right
        · cases left.symm.trans (code.trans right)
        · rename_i d
          cases Option.some.inj (left.symm.trans (code.trans right))
          have nextA := ByteArray.le_size_of_utf8DecodeChar?_eq_some left
          have nextB := ByteArray.le_size_of_utf8DecodeChar?_eq_some right
          have rest := congrArg (fun r : ByteArray => r.extract c.utf8Size r.size) suffix
          rw [shift_from a _ _ hi, shift_from b _ _ hj] at rest
          have smaller : a.size - (i + c.utf8Size) < a.size - i :=
            Nat.sub_lt_sub_left ha (Nat.lt_add_of_pos_right c.utf8Size_pos)
          have pushed : (front ++ acc).push c = front ++ acc.push c := by
            apply Array.ext'
            rw [Array.toList_push, Array.toList_append, Array.toList_append, Array.toList_push, List.append_assoc]
          rw [pushed]
          apply ih _ _ nextA nextB (acc.push c) (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le smaller room)) rest
    · rw [ite_eq_right ha, ite_eq_right (fun h => ha ((same_suffix_bound suffix).2 h))]
      rfl

public theorem ByteArray.utf8Decode?go_eq_utf8Decode?go_extract :
    type_of% (private_decl% @_root_.ByteArray.utf8Decode?go_eq_utf8Decode?go_extract) := by
  intro i b hi acc
  have same := decode_same_suffix (b.size - i) (a := b) (b := b.extract i b.size)
    i 0 hi (Nat.zero_le _) acc #[] (Nat.le_refl _) (_root_.ByteArray.extract_zero_size.symm)
  rw [Array.append_empty] at same
  exact same

public theorem ByteArray.utf8Decode?_utf8Encode_singleton_append :
    type_of% @_root_.ByteArray.utf8Decode?_utf8Encode_singleton_append := by
  intro tail c
  let b := [c].utf8Encode ++ tail
  have hsize : [c].utf8Encode.size = c.utf8Size := by
    rw [List.utf8Encode_singleton, List.size_toByteArray, _root_.String.length_utf8EncodeChar]
  have first : b.utf8DecodeChar? 0 = some c := _root_.List.utf8DecodeChar?_utf8Encode_singleton_append
  have fits := _root_.ByteArray.le_size_of_utf8DecodeChar?_eq_some first
  have hpos : 0 < b.size := Nat.lt_of_lt_of_le c.utf8Size_pos (by simpa only [Nat.zero_add] using fits)
  show b.utf8Decode? = _
  unfold _root_.ByteArray.utf8Decode?
  rw [_root_.ByteArray.utf8Decode?.go.eq_1 b, ite_eq_left hpos]
  split
  · rename_i noneEq
    cases noneEq.symm.trans first
  · rename_i d someEq
    cases Option.some.inj (someEq.symm.trans first)
    have rest : b.extract (0 + c.utf8Size) b.size = tail.extract 0 tail.size := by
      rw [_root_.ByteArray.extract_zero_size, Nat.zero_add]
      exact _root_.ByteArray.extract_append_eq_right hsize.symm _root_.ByteArray.size_append
    have same := decode_same_suffix (b.size - (0 + c.utf8Size)) (a := b) (b := tail)
      (0 + c.utf8Size) 0 fits (Nat.zero_le _) #[c] #[] (Nat.le_refl _) rest
    rw [Array.append_empty] at same
    exact same

private theorem decode_encoded_tail (xs : List Char) {b : ByteArray} (i : Nat) (hi : i ≤ b.size)
    (acc : Array Char) (suffix : b.extract i b.size = xs.utf8Encode) :
    ByteArray.utf8Decode?.go b i acc hi = some (acc.toList ++ xs).toArray := by
  have measured : (b.extract i b.size).size = b.size - i :=
    ByteArray.size_extract.trans (congrArg (· - i) (Nat.min_self _))
  induction xs generalizing i acc with
  | nil =>
    have stop : b.size - i = 0 := measured.symm.trans (congrArg ByteArray.size suffix)
    rw [ByteArray.utf8Decode?.go.eq_1, ite_eq_right (Nat.not_lt_of_ge (Nat.le_of_sub_eq_zero stop)),
      List.append_nil, Array.toArray_toList]
  | cons c xs ih =>
    have headSize : [c].utf8Encode.size = c.utf8Size := by
      rw [List.utf8Encode_singleton, List.size_toByteArray, String.length_utf8EncodeChar]
    have code : b.utf8DecodeChar? i = some c := by
      rw [_root_.ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract, suffix,
        List.utf8DecodeChar?_utf8Encode_cons]
    have next := ByteArray.le_size_of_utf8DecodeChar?_eq_some code
    have hpos : i < b.size :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right c.utf8Size_pos) next
    have rest : b.extract (i + c.utf8Size) b.size = xs.utf8Encode := calc
      _ = (b.extract i b.size).extract c.utf8Size (b.extract i b.size).size := by
        rw [ByteArray.extract_extract, measured, Nat.add_sub_of_le hi, Nat.min_self]
      _ = _ := by
        rw [suffix, List.utf8Encode_cons, ByteArray.extract_append_eq_right headSize.symm]
        exact ByteArray.size_append
    rw [ByteArray.utf8Decode?.go.eq_1, ite_eq_left hpos]
    split
    · rename_i failed
      cases failed.symm.trans code
    · rename_i d got
      cases Option.some.inj (got.symm.trans code)
      rw [ih _ next (acc.push c) rest (ByteArray.size_extract.trans
        (congrArg (· - _) (Nat.min_self _))), Array.toList_push, List.append_assoc]
      rfl

public theorem List.utf8Decode?_utf8Encode : type_of% @_root_.List.utf8Decode?_utf8Encode := by
  intro l
  exact decode_encoded_tail l 0 (Nat.zero_le _) #[] ByteArray.extract_zero_size

public theorem String.Internal.toArray._proof_1 :
    type_of% (private_decl% @_root_.String.Internal.toArray._proof_1) := by
  intro s
  obtain ⟨l, h⟩ := s.isValidUTF8
  rw [h, _root_.List.utf8Decode?_utf8Encode]
  rfl

end OmegaChecks.InitPort.Alternatives
