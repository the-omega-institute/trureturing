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

end OmegaChecks.InitPort.Alternatives
