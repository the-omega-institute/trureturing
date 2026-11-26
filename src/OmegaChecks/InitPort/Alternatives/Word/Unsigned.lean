module
import all Init.SizeOfLemmas
import all Init.SizeOf

public import OmegaChecks.InitPort.Alternatives.Word.BitVec
import all Init.Data.UInt.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem UInt16.toNat_toUInt32 : type_of% @_root_.UInt16.toNat_toUInt32 := by
  intro x
  exact (_root_.UInt32.toFin_val x.toUInt32).symm.trans ((congrArg Fin.val (_root_.UInt16.toFin_toUInt32 x)).trans
    ((Fin.val_castLE _ _).trans (_root_.UInt16.toFin_val x)))

public theorem UInt16.toNat_toUInt64 : type_of% @_root_.UInt16.toNat_toUInt64 := by
  intro x
  exact (_root_.UInt64.toFin_val x.toUInt64).symm.trans ((congrArg Fin.val (_root_.UInt16.toFin_toUInt64 x)).trans
    ((Fin.val_castLE _ _).trans (_root_.UInt16.toFin_val x)))

public theorem UInt32.toNat_toUInt64 : type_of% @_root_.UInt32.toNat_toUInt64 := by
  intro x
  exact (_root_.UInt64.toFin_val x.toUInt64).symm.trans ((congrArg Fin.val (_root_.UInt32.toFin_toUInt64 x)).trans
    ((Fin.val_castLE _ _).trans (_root_.UInt32.toFin_val x)))

private theorem mod_eq_pred_of_dvd_succ {d n : Nat} (hd : 0 < d) (dvd : d ∣ n+1) :
    n % d = d-1 := by
  have wrap : (n % d + 1) % d = 0 := (Nat.mod_add_mod ..).trans (Nat.mod_eq_zero_of_dvd dvd)
  have lt := Nat.mod_lt n hd
  by_cases eq : n % d = d-1
  · exact eq
  · have small : n % d + 1 < d := by omega
    rw [Nat.mod_eq_of_lt small] at wrap
    omega

private theorem pred_mod_of_dvd {d n : Nat} (hd : 0 < d) (hn : 0 < n) (dvd : d ∣ n) :
    (n-1) % d = d-1 :=
  mod_eq_pred_of_dvd_succ hd (Nat.sub_add_cancel hn ▸ dvd)

public theorem UInt8.size_dvd_usizeSize : type_of% @_root_.UInt8.size_dvd_usizeSize :=
  Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 8 ≤ 32) System.Platform.le_numBits)

public theorem USize.size_sub_one_mod_uint8Size : type_of% @_root_.USize.size_sub_one_mod_uint8Size :=
  pred_mod_of_dvd (Nat.two_pow_pos 8) _root_.USize.size_pos UInt8.size_dvd_usizeSize

public theorem UInt16.size_dvd_usizeSize : type_of% @_root_.UInt16.size_dvd_usizeSize :=
  Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 16 ≤ 32) System.Platform.le_numBits)

public theorem USize.size_sub_one_mod_uint16Size : type_of% @_root_.USize.size_sub_one_mod_uint16Size :=
  pred_mod_of_dvd (Nat.two_pow_pos 16) _root_.USize.size_pos UInt16.size_dvd_usizeSize

public theorem UInt32.size_dvd_usizeSize : type_of% @_root_.UInt32.size_dvd_usizeSize :=
  Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 32 ≤ 32) System.Platform.le_numBits)

public theorem USize.size_sub_one_mod_uint32Size : type_of% @_root_.USize.size_sub_one_mod_uint32Size :=
  pred_mod_of_dvd (Nat.two_pow_pos 32) _root_.USize.size_pos UInt32.size_dvd_usizeSize

public theorem USize.size_dvd_uInt64Size : type_of% @_root_.USize.size_dvd_uInt64Size :=
  Nat.pow_dvd_pow 2 System.Platform.numBits_le

private def onesMask : Nat → Nat
  | 0 => 0
  | n+1 => (onesMask n * 2).succ

private theorem succ_onesMask (n : Nat) : (onesMask n).succ = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [onesMask, Nat.pow_succ, ← ih, Nat.succ_mul]

public theorem UInt64.size_sub_one_mod_uSizeSize : type_of% @_root_.UInt64.size_sub_one_mod_uSizeSize := by
  have successor : 18446744073709551615 + 1 = UInt64.size := succ_onesMask 64
  exact mod_eq_pred_of_dvd_succ _root_.USize.size_pos (successor ▸ USize.size_dvd_uInt64Size)

public theorem UInt16.toUInt32_add : type_of% @_root_.UInt16.toUInt32_add := by
  intro a b
  apply _root_.UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, _root_.UInt16.toNat_add, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_add, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]
  rw [_root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))).symm

public theorem UInt16.toUInt32_mul : type_of% @_root_.UInt16.toUInt32_mul := by
  intro a b
  apply _root_.UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, _root_.UInt16.toNat_mul, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_mul, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]
  rw [_root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))).symm

public theorem UInt16.toUInt32_div : type_of% @_root_.UInt16.toUInt32_div := by
  intro a b
  apply _root_.UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, _root_.UInt16.toNat_div, _root_.UInt32.toNat_div,
    UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]

public theorem UInt16.toUInt32_mod : type_of% @_root_.UInt16.toUInt32_mod := by
  intro a b
  apply _root_.UInt32.toNat.inj
  rw [UInt16.toNat_toUInt32, _root_.UInt16.toNat_mod, _root_.UInt32.toNat_mod,
    UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]

public theorem UInt16.toUInt64_add : type_of% @_root_.UInt16.toUInt64_add := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, _root_.UInt16.toNat_add, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_add, UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]
  rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 64))).symm

public theorem UInt16.toUInt64_mul : type_of% @_root_.UInt16.toUInt64_mul := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, _root_.UInt16.toNat_mul, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_mul, UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]
  rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 64))).symm

public theorem UInt16.toUInt64_div : type_of% @_root_.UInt16.toUInt64_div := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, _root_.UInt16.toNat_div, _root_.UInt64.toNat_div,
    UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]

public theorem UInt16.toUInt64_mod : type_of% @_root_.UInt16.toUInt64_mod := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt16.toNat_toUInt64, _root_.UInt16.toNat_mod, _root_.UInt64.toNat_mod,
    UInt16.toNat_toUInt64, UInt16.toNat_toUInt64]

public theorem UInt32.toUInt64_add : type_of% @_root_.UInt32.toUInt64_add := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, _root_.UInt32.toNat_add, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 32 ≤ 64))).symm

public theorem UInt32.toUInt64_mul : type_of% @_root_.UInt32.toUInt64_mul := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, _root_.UInt32.toNat_mul, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 32 ≤ 64))).symm

public theorem UInt32.toUInt64_div : type_of% @_root_.UInt32.toUInt64_div := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, _root_.UInt32.toNat_div, _root_.UInt64.toNat_div,
    UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]

public theorem UInt32.toUInt64_mod : type_of% @_root_.UInt32.toUInt64_mod := by
  intro a b
  apply _root_.UInt64.toNat.inj
  rw [UInt32.toNat_toUInt64, _root_.UInt32.toNat_mod, _root_.UInt64.toNat_mod,
    UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]

private theorem ofNat_emod_toNat_eq_ofInt (w : Nat) (z : Int) :
    _root_.BitVec.ofNat w (z % (2^w : Int)).toNat = _root_.BitVec.ofInt w z := by
  apply _root_.BitVec.eq_of_toNat_eq
  rw [_root_.BitVec.toNat_ofNat, _root_.BitVec.toNat_ofInt]
  apply Nat.mod_eq_of_lt
  exact (_root_.BitVec.ofInt w z).isLt

private theorem uint16_toBitVec_ofInt (z : Int) : (_root_.UInt16.ofInt z).toBitVec = _root_.BitVec.ofInt 16 z :=
  (_root_.UInt16.toBitVec_ofNat' _).trans (ofNat_emod_toNat_eq_ofInt 16 z)

public theorem UInt16.ofInt_add : type_of% @_root_.UInt16.ofInt_add := by
  intro x y
  apply _root_.UInt16.toBitVec_inj.mp
  rw [uint16_toBitVec_ofInt, _root_.UInt16.toBitVec_add, uint16_toBitVec_ofInt, uint16_toBitVec_ofInt, _root_.BitVec.ofInt_add]

public theorem UInt16.ofInt_mul : type_of% @_root_.UInt16.ofInt_mul := by
  intro x y
  apply _root_.UInt16.toBitVec_inj.mp
  rw [uint16_toBitVec_ofInt, _root_.UInt16.toBitVec_mul, uint16_toBitVec_ofInt, uint16_toBitVec_ofInt, _root_.BitVec.ofInt_mul]

private theorem uint32_toBitVec_ofInt (z : Int) : (_root_.UInt32.ofInt z).toBitVec = _root_.BitVec.ofInt 32 z :=
  (_root_.UInt32.toBitVec_ofNat' _).trans (ofNat_emod_toNat_eq_ofInt 32 z)

public theorem UInt32.ofInt_add : type_of% @_root_.UInt32.ofInt_add := by
  intro x y
  apply _root_.UInt32.toBitVec_inj.mp
  rw [uint32_toBitVec_ofInt, _root_.UInt32.toBitVec_add, uint32_toBitVec_ofInt, uint32_toBitVec_ofInt, _root_.BitVec.ofInt_add]

public theorem UInt32.ofInt_mul : type_of% @_root_.UInt32.ofInt_mul := by
  intro x y
  apply _root_.UInt32.toBitVec_inj.mp
  rw [uint32_toBitVec_ofInt, _root_.UInt32.toBitVec_mul, uint32_toBitVec_ofInt, uint32_toBitVec_ofInt, _root_.BitVec.ofInt_mul]

private theorem uint64_toBitVec_ofInt (z : Int) : (_root_.UInt64.ofInt z).toBitVec = _root_.BitVec.ofInt 64 z :=
  (_root_.UInt64.toBitVec_ofNat' _).trans (ofNat_emod_toNat_eq_ofInt 64 z)

public theorem UInt64.ofInt_add : type_of% @_root_.UInt64.ofInt_add := by
  intro x y
  apply _root_.UInt64.toBitVec_inj.mp
  rw [uint64_toBitVec_ofInt, _root_.UInt64.toBitVec_add, uint64_toBitVec_ofInt, uint64_toBitVec_ofInt, _root_.BitVec.ofInt_add]

public theorem UInt64.ofInt_mul : type_of% @_root_.UInt64.ofInt_mul := by
  intro x y
  apply _root_.UInt64.toBitVec_inj.mp
  rw [uint64_toBitVec_ofInt, _root_.UInt64.toBitVec_mul, uint64_toBitVec_ofInt, uint64_toBitVec_ofInt, _root_.BitVec.ofInt_mul]

private theorem usize_toBitVec_ofInt (z : Int) : (_root_.USize.ofInt z).toBitVec = _root_.BitVec.ofInt System.Platform.numBits z :=
  (_root_.USize.toBitVec_ofNat' _).trans (ofNat_emod_toNat_eq_ofInt System.Platform.numBits z)

public theorem USize.ofInt_add : type_of% @_root_.USize.ofInt_add := by
  intro x y
  apply _root_.USize.toBitVec_inj.mp
  rw [usize_toBitVec_ofInt, _root_.USize.toBitVec_add, usize_toBitVec_ofInt, usize_toBitVec_ofInt, _root_.BitVec.ofInt_add]

public theorem USize.ofInt_mul : type_of% @_root_.USize.ofInt_mul := by
  intro x y
  apply _root_.USize.toBitVec_inj.mp
  rw [usize_toBitVec_ofInt, _root_.USize.toBitVec_mul, usize_toBitVec_ofInt, usize_toBitVec_ofInt, _root_.BitVec.ofInt_mul]

public theorem UInt8.div_self : type_of% @_root_.UInt8.div_self := by
  intro a
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    apply _root_.UInt8.toNat.inj
    rw [_root_.UInt8.toNat_div]
    exact (Nat.div_self (Nat.pos_of_ne_zero (fun z => h (_root_.UInt8.toNat.inj z)))).trans _root_.UInt8.toNat_one.symm

public theorem UInt16.div_self : type_of% @_root_.UInt16.div_self := by
  intro a
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    apply _root_.UInt16.toNat.inj
    rw [_root_.UInt16.toNat_div]
    exact (Nat.div_self (Nat.pos_of_ne_zero (fun z => h (_root_.UInt16.toNat.inj z)))).trans _root_.UInt16.toNat_one.symm

public theorem UInt32.div_self : type_of% @_root_.UInt32.div_self := by
  intro a
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    apply _root_.UInt32.toNat.inj
    rw [_root_.UInt32.toNat_div]
    exact (Nat.div_self (Nat.pos_of_ne_zero (fun z => h (_root_.UInt32.toNat.inj z)))).trans _root_.UInt32.toNat_one.symm

public theorem UInt64.div_self : type_of% @_root_.UInt64.div_self := by
  intro a
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    apply _root_.UInt64.toNat.inj
    rw [_root_.UInt64.toNat_div]
    exact (Nat.div_self (Nat.pos_of_ne_zero (fun z => h (_root_.UInt64.toNat.inj z)))).trans _root_.UInt64.toNat_one.symm

public theorem USize.div_self : type_of% @_root_.USize.div_self := by
  intro a
  by_cases h : a = 0
  · subst a
    rw [ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    apply _root_.USize.toNat.inj
    rw [_root_.USize.toNat_div]
    exact (Nat.div_self (Nat.pos_of_ne_zero (fun z => h (_root_.USize.toNat.inj z)))).trans _root_.USize.toNat_one.symm

public theorem UInt32.toUInt16_le : type_of% @_root_.UInt32.toUInt16_le := by
  intro a b
  apply _root_.UInt16.le_iff_toNat_le.trans
  apply Iff.trans _ _root_.UInt32.le_iff_toNat_le.symm
  rw [_root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_mod, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]

public theorem UInt32.toUInt16_lt : type_of% @_root_.UInt32.toUInt16_lt := by
  intro a b
  apply _root_.UInt16.lt_iff_toNat_lt.trans
  apply Iff.trans _ _root_.UInt32.lt_iff_toNat_lt.symm
  rw [_root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_mod, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]

public theorem UInt64.toUInt16_le : type_of% @_root_.UInt64.toUInt16_le := by
  intro a b
  apply _root_.UInt16.le_iff_toNat_le.trans
  apply Iff.trans _ _root_.UInt64.le_iff_toNat_le.symm
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]

public theorem UInt64.toUInt16_lt : type_of% @_root_.UInt64.toUInt16_lt := by
  intro a b
  apply _root_.UInt16.lt_iff_toNat_lt.trans
  apply Iff.trans _ _root_.UInt64.lt_iff_toNat_lt.symm
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]

public theorem UInt64.toUInt32_le : type_of% @_root_.UInt64.toUInt32_le := by
  intro a b
  apply _root_.UInt32.le_iff_toNat_le.trans
  apply Iff.trans _ _root_.UInt64.le_iff_toNat_le.symm
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]

public theorem UInt64.toUInt32_lt : type_of% @_root_.UInt64.toUInt32_lt := by
  intro a b
  apply _root_.UInt32.lt_iff_toNat_lt.trans
  apply Iff.trans _ _root_.UInt64.lt_iff_toNat_lt.symm
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]

public theorem UInt32.toFin_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt32.toFin_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 32))

public theorem UInt64.toUSize_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt64.toUSize_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos System.Platform.numBits))

public theorem UInt32.toBitVec_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt32.toBitVec_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 32))

public theorem UInt32.toUInt64_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt32.toUInt64_ofNatClamp_of_le._proof_1 :=
  Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 32)) (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 32 ≤ 64))

public theorem UInt16.toBitVec_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt16.toBitVec_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 16))

public theorem USize.toFin_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.USize.toFin_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos System.Platform.numBits))

public theorem UInt64.toBitVec_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt64.toBitVec_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 64))

public theorem UInt64.toFin_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt64.toFin_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 64))

public theorem UInt32.toUInt16_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt32.toUInt16_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 16))

public theorem UInt64.toUInt32_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt64.toUInt32_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 32))

public theorem UInt16.toUInt64_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt16.toUInt64_ofNatClamp_of_le._proof_1 :=
  Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 16)) (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 16 ≤ 64))

public theorem USize.toBitVec_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.USize.toBitVec_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos System.Platform.numBits))

public theorem UInt16.toFin_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt16.toFin_ofNatClamp_of_le._proof_1 :=
  (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 16))

public theorem USize.toUInt64_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.USize.toUInt64_ofNatClamp_of_le._proof_1 :=
  Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt (Nat.two_pow_pos System.Platform.numBits)) _root_.USize.size_le_uint64Size

public theorem UInt16.toUInt32_ofNatClamp_of_le._proof_1 :
    type_of% @_root_.UInt16.toUInt32_ofNatClamp_of_le._proof_1 :=
  Nat.lt_of_lt_of_le (Nat.sub_one_lt_of_lt (Nat.two_pow_pos 16)) (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 16 ≤ 32))

public theorem UInt16.ofNat_size : type_of% @_root_.UInt16.ofNat_size := by
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt16.toNat_ofNat', _root_.UInt16.toNat_zero]
  exact Nat.mod_self _

public theorem UInt32.ofNat_size : type_of% @_root_.UInt32.ofNat_size := by
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt32.toNat_ofNat', _root_.UInt32.toNat_zero]
  exact Nat.mod_self _

public theorem UInt64.ofNat_size : type_of% @_root_.UInt64.ofNat_size := by
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt64.toNat_ofNat', _root_.UInt64.toNat_zero]
  exact Nat.mod_self _

public theorem UInt32.toUInt16_div : type_of% @_root_.UInt32.toUInt16_div := by
  intro a b ha hb
  have bound (z : UInt32) (h : z < 65536) : z.toNat < 2 ^ 16 := by
    have aux := _root_.UInt32.lt_iff_toNat_lt.mp h
    rw [_root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))] at aux
    exact aux
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_div, _root_.UInt16.toNat_div,
    _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_toUInt16]
  exact Nat.div_mod_eq_mod_div_mod (bound a ha) (bound b hb)

public theorem UInt32.toUInt16_mod : type_of% @_root_.UInt32.toUInt16_mod := by
  intro a b ha hb
  have bound (z : UInt32) (h : z < 65536) : z.toNat < 2 ^ 16 := by
    have aux := _root_.UInt32.lt_iff_toNat_lt.mp h
    rw [_root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))] at aux
    exact aux
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_mod, _root_.UInt16.toNat_mod,
    _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_toUInt16]
  exact Nat.mod_mod_eq_mod_mod_mod (bound a ha) (bound b hb)

public theorem UInt64.toUInt16_div : type_of% @_root_.UInt64.toUInt16_div := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 65536) : z.toNat < 2 ^ 16 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))] at aux
    exact aux
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_div, _root_.UInt16.toNat_div,
    _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_toUInt16]
  exact Nat.div_mod_eq_mod_div_mod (bound a ha) (bound b hb)

public theorem UInt64.toUInt16_mod : type_of% @_root_.UInt64.toUInt16_mod := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 65536) : z.toNat < 2 ^ 16 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))] at aux
    exact aux
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_mod, _root_.UInt16.toNat_mod,
    _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_toUInt16]
  exact Nat.mod_mod_eq_mod_mod_mod (bound a ha) (bound b hb)

public theorem UInt64.toUInt32_div : type_of% @_root_.UInt64.toUInt32_div := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 4294967296) : z.toNat < 2 ^ 32 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))] at aux
    exact aux
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_div, _root_.UInt32.toNat_div,
    _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32]
  exact Nat.div_mod_eq_mod_div_mod (bound a ha) (bound b hb)

public theorem UInt64.toUInt32_mod : type_of% @_root_.UInt64.toUInt32_mod := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 4294967296) : z.toNat < 2 ^ 32 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))] at aux
    exact aux
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_mod, _root_.UInt32.toNat_mod,
    _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32]
  exact Nat.mod_mod_eq_mod_mod_mod (bound a ha) (bound b hb)

public theorem UInt64.toUSize_div : type_of% @_root_.UInt64.toUSize_div := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 4294967296) : z.toNat < 2 ^ 32 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))] at aux
    exact aux
  exact _root_.UInt64.toUSize_div_of_toNat_lt a b (Nat.lt_of_lt_of_le (bound a ha) _root_.UInt32.size_le_usizeSize)
    (Nat.lt_of_lt_of_le (bound b hb) _root_.UInt32.size_le_usizeSize)

public theorem UInt64.toUSize_mod : type_of% @_root_.UInt64.toUSize_mod := by
  intro a b ha hb
  have bound (z : UInt64) (h : z < 4294967296) : z.toNat < 2 ^ 32 := by
    have aux := _root_.UInt64.lt_iff_toNat_lt.mp h
    rw [_root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))] at aux
    exact aux
  exact _root_.UInt64.toUSize_mod_of_toNat_lt a b (Nat.lt_of_lt_of_le (bound a ha) _root_.UInt32.size_le_usizeSize)
    (Nat.lt_of_lt_of_le (bound b hb) _root_.UInt32.size_le_usizeSize)

public theorem UInt16.ofInt_neg_one : type_of% @_root_.UInt16.ofInt_neg_one := by
  apply _root_.UInt16.toBitVec_inj.mp
  rw [uint16_toBitVec_ofInt, _root_.UInt16.toBitVec_neg, _root_.BitVec.ofInt_neg]
  exact congrArg Neg.neg ((uint16_toBitVec_ofInt 1).symm.trans
    (congrArg _root_.UInt16.toBitVec _root_.UInt16.ofInt_one))

public theorem UInt32.ofInt_neg_one : type_of% @_root_.UInt32.ofInt_neg_one := by
  apply _root_.UInt32.toBitVec_inj.mp
  rw [uint32_toBitVec_ofInt, _root_.UInt32.toBitVec_neg, _root_.BitVec.ofInt_neg]
  exact congrArg Neg.neg ((uint32_toBitVec_ofInt 1).symm.trans
    (congrArg _root_.UInt32.toBitVec _root_.UInt32.ofInt_one))

public theorem UInt64.ofInt_neg_one : type_of% @_root_.UInt64.ofInt_neg_one := by
  apply _root_.UInt64.toBitVec_inj.mp
  rw [uint64_toBitVec_ofInt, _root_.UInt64.toBitVec_neg, _root_.BitVec.ofInt_neg]
  exact congrArg Neg.neg ((uint64_toBitVec_ofInt 1).symm.trans
    (congrArg _root_.UInt64.toBitVec _root_.UInt64.ofInt_one))

public theorem USize.ofInt_one : type_of% @_root_.USize.ofInt_one := by
  apply _root_.USize.toBitVec_inj.mp
  rw [usize_toBitVec_ofInt, _root_.USize.toBitVec_ofNat 1]
  exact _root_.BitVec.ofInt_natCast _ 1

public theorem USize.ofInt_neg_one : type_of% @_root_.USize.ofInt_neg_one := by
  apply _root_.USize.toBitVec_inj.mp
  rw [usize_toBitVec_ofInt, _root_.USize.toBitVec_neg, _root_.BitVec.ofInt_neg]
  exact congrArg Neg.neg ((usize_toBitVec_ofInt 1).symm.trans
    (congrArg _root_.USize.toBitVec USize.ofInt_one))

public theorem UInt64.toUSize_ofNatClamp_of_le : type_of% @_root_.UInt64.toUSize_ofNatClamp_of_le := by
  intro n hn
  apply _root_.USize.toNat.inj
  rw [_root_.UInt64.toNat_toUSize, _root_.UInt64.toNat_ofNatClamp_of_le hn, _root_.USize.toNat_ofNatLT]
  exact pred_mod_of_dvd _root_.USize.size_pos (Nat.two_pow_pos 64) USize.size_dvd_uInt64Size

public theorem USize.ofNat_uInt64Size_sub_one : type_of% @_root_.USize.ofNat_uInt64Size_sub_one := by
  apply _root_.USize.toNat.inj
  exact _root_.USize.toNat_ofNat'.trans ((pred_mod_of_dvd _root_.USize.size_pos (Nat.two_pow_pos 64)
    USize.size_dvd_uInt64Size).trans _root_.USize.toNat_ofNatLT.symm)

private theorem oneAddSize (n : Nat) : 1 + n = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem wordSize (x : BitVec w) : 1 + sizeOf x = x.toNat + 3 := by
  rw [BitVec.sizeOf, Fin.sizeOf, oneAddSize]
  rfl

public theorem UInt8.sizeOf : type_of% @_root_.UInt8.sizeOf := fun ⟨x⟩ => wordSize x

public theorem UInt16.sizeOf : type_of% @_root_.UInt16.sizeOf := fun ⟨x⟩ => wordSize x

public theorem UInt32.sizeOf : type_of% @_root_.UInt32.sizeOf := fun ⟨x⟩ => wordSize x

public theorem UInt64.sizeOf : type_of% @_root_.UInt64.sizeOf := fun ⟨x⟩ => wordSize x

public theorem USize.sizeOf : type_of% @_root_.USize.sizeOf := fun ⟨x⟩ => wordSize x

public theorem Char.sizeOf : type_of% @_root_.Char.sizeOf := by
  intro ⟨x, _⟩
  change 1 + SizeOf.sizeOf x = x.toNat + 4
  rw [UInt32.sizeOf, oneAddSize]

end OmegaChecks.InitPort.Alternatives
