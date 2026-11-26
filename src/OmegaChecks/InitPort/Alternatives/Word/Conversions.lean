module

public import OmegaChecks.InitPort.Alternatives.Word.Unsigned

namespace OmegaChecks.InitPort.Alternatives

private theorem toNat_neg_one_8 : (-1 : UInt8).toNat = UInt8.size - 1 := by
  rw [← _root_.UInt8.toNat_toBitVec, _root_.UInt8.toBitVec_neg, _root_.UInt8.toBitVec_one,
    _root_.BitVec.neg_one_eq_allOnes]
  exact _root_.BitVec.toNat_allOnes

private theorem toNat_neg_one_16 : (-1 : UInt16).toNat = UInt16.size - 1 := by
  rw [← _root_.UInt16.toNat_toBitVec, _root_.UInt16.toBitVec_neg, _root_.UInt16.toBitVec_one,
    _root_.BitVec.neg_one_eq_allOnes]
  exact _root_.BitVec.toNat_allOnes

private theorem toNat_neg_one_32 : (-1 : UInt32).toNat = UInt32.size - 1 := by
  rw [← _root_.UInt32.toNat_toBitVec, _root_.UInt32.toBitVec_neg, _root_.UInt32.toBitVec_one,
    _root_.BitVec.neg_one_eq_allOnes]
  exact _root_.BitVec.toNat_allOnes

private theorem toNat_neg_one_64 : (-1 : UInt64).toNat = UInt64.size - 1 := by
  rw [← _root_.UInt64.toNat_toBitVec, _root_.UInt64.toBitVec_neg, _root_.UInt64.toBitVec_one,
    _root_.BitVec.neg_one_eq_allOnes]
  exact _root_.BitVec.toNat_allOnes

public theorem UInt16.toBitVec_ofNatClamp_of_le : type_of% @_root_.UInt16.toBitVec_ofNatClamp_of_le := by
  intro n hn
  exact _root_.BitVec.eq_of_toNat_eq ((_root_.UInt16.toNat_toBitVec _).trans (_root_.UInt16.toNat_ofNatClamp_of_le hn))

public theorem UInt16.toFin_ofNatClamp_of_le : type_of% @_root_.UInt16.toFin_ofNatClamp_of_le := by
  intro n hn
  exact Fin.ext ((_root_.UInt16.toFin_val _).trans (_root_.UInt16.toNat_ofNatClamp_of_le hn))

public theorem UInt16.toUInt32_ofNatClamp_of_le : type_of% @_root_.UInt16.toUInt32_ofNatClamp_of_le := by
  intro n hn
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt16.toNat_toUInt32, _root_.UInt16.toNat_ofNatClamp_of_le hn, _root_.UInt32.toNat_ofNatLT]

public theorem UInt16.toUInt64_ofNatClamp_of_le : type_of% @_root_.UInt16.toUInt64_ofNatClamp_of_le := by
  intro n hn
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt16.toNat_toUInt64, _root_.UInt16.toNat_ofNatClamp_of_le hn, _root_.UInt64.toNat_ofNatLT]

public theorem UInt16.toUInt8_ofNatClamp_of_le : type_of% @_root_.UInt16.toUInt8_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt16.ofNatClamp n = -1 :=
    _root_.UInt16.toNat.inj ((_root_.UInt16.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_16.symm)
  rw [saturated, _root_.UInt16.toUInt8_neg, _root_.UInt16.toUInt8_ofNat (n := 1)]
  exact _root_.UInt8.toNat.inj (toNat_neg_one_8.trans _root_.UInt8.toNat_ofNatLT.symm)

public theorem UInt16.toUSize_ofNatClamp_of_le : type_of% @_root_.UInt16.toUSize_ofNatClamp_of_le := by
  intro n hn
  apply _root_.USize.toNat.inj
  rw [_root_.UInt16.toNat_toUSize, _root_.UInt16.toNat_ofNatClamp_of_le hn, _root_.USize.toNat_ofNatLT]

public theorem UInt32.toBitVec_ofNatClamp_of_le : type_of% @_root_.UInt32.toBitVec_ofNatClamp_of_le := by
  intro n hn
  exact _root_.BitVec.eq_of_toNat_eq ((_root_.UInt32.toNat_toBitVec _).trans (_root_.UInt32.toNat_ofNatClamp_of_le hn))

public theorem UInt32.toFin_ofNatClamp_of_le : type_of% @_root_.UInt32.toFin_ofNatClamp_of_le := by
  intro n hn
  exact Fin.ext ((_root_.UInt32.toFin_val _).trans (_root_.UInt32.toNat_ofNatClamp_of_le hn))

public theorem UInt32.toUInt16_ofNatClamp_of_le : type_of% @_root_.UInt32.toUInt16_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt32.ofNatClamp n = -1 :=
    _root_.UInt32.toNat.inj ((_root_.UInt32.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_32.symm)
  rw [saturated, _root_.UInt32.toUInt16_neg, _root_.UInt32.toUInt16_ofNat (n := 1)]
  exact _root_.UInt16.toNat.inj (toNat_neg_one_16.trans _root_.UInt16.toNat_ofNatLT.symm)

public theorem UInt32.toUInt64_ofNatClamp_of_le : type_of% @_root_.UInt32.toUInt64_ofNatClamp_of_le := by
  intro n hn
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_ofNatClamp_of_le hn, _root_.UInt64.toNat_ofNatLT]

public theorem UInt32.toUInt8_ofNatClamp_of_le : type_of% @_root_.UInt32.toUInt8_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt32.ofNatClamp n = -1 :=
    _root_.UInt32.toNat.inj ((_root_.UInt32.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_32.symm)
  rw [saturated, _root_.UInt32.toUInt8_neg, _root_.UInt32.toUInt8_ofNat (n := 1)]
  exact _root_.UInt8.toNat.inj (toNat_neg_one_8.trans _root_.UInt8.toNat_ofNatLT.symm)

public theorem UInt32.toUSize_ofNatClamp_of_le : type_of% @_root_.UInt32.toUSize_ofNatClamp_of_le := by
  intro n hn
  apply _root_.USize.toNat.inj
  rw [_root_.UInt32.toNat_toUSize, _root_.UInt32.toNat_ofNatClamp_of_le hn, _root_.USize.toNat_ofNatLT]

public theorem UInt64.toBitVec_ofNatClamp_of_le : type_of% @_root_.UInt64.toBitVec_ofNatClamp_of_le := by
  intro n hn
  exact _root_.BitVec.eq_of_toNat_eq ((_root_.UInt64.toNat_toBitVec _).trans (_root_.UInt64.toNat_ofNatClamp_of_le hn))

public theorem UInt64.toFin_ofNatClamp_of_le : type_of% @_root_.UInt64.toFin_ofNatClamp_of_le := by
  intro n hn
  exact Fin.ext ((_root_.UInt64.toFin_val _).trans (_root_.UInt64.toNat_ofNatClamp_of_le hn))

public theorem UInt64.toUInt16_ofNatClamp_of_le : type_of% @_root_.UInt64.toUInt16_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt64.ofNatClamp n = -1 :=
    _root_.UInt64.toNat.inj ((_root_.UInt64.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_64.symm)
  rw [saturated, _root_.UInt64.toUInt16_neg, _root_.UInt64.toUInt16_ofNat (n := 1)]
  exact _root_.UInt16.toNat.inj (toNat_neg_one_16.trans _root_.UInt16.toNat_ofNatLT.symm)

public theorem UInt64.toUInt32_ofNatClamp_of_le : type_of% @_root_.UInt64.toUInt32_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt64.ofNatClamp n = -1 :=
    _root_.UInt64.toNat.inj ((_root_.UInt64.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_64.symm)
  rw [saturated, _root_.UInt64.toUInt32_neg, _root_.UInt64.toUInt32_ofNat (n := 1)]
  exact _root_.UInt32.toNat.inj (toNat_neg_one_32.trans _root_.UInt32.toNat_ofNatLT.symm)

public theorem UInt64.toUInt8_ofNatClamp_of_le : type_of% @_root_.UInt64.toUInt8_ofNatClamp_of_le := by
  intro n hn
  have saturated : UInt64.ofNatClamp n = -1 :=
    _root_.UInt64.toNat.inj ((_root_.UInt64.toNat_ofNatClamp_of_le hn).trans toNat_neg_one_64.symm)
  rw [saturated, _root_.UInt64.toUInt8_neg, _root_.UInt64.toUInt8_ofNat (n := 1)]
  exact _root_.UInt8.toNat.inj (toNat_neg_one_8.trans _root_.UInt8.toNat_ofNatLT.symm)

public theorem USize.toUInt16_ofNatClamp_of_le : type_of% @_root_.USize.toUInt16_ofNatClamp_of_le := by
  intro n hn
  apply _root_.UInt16.toNat.inj
  rw [_root_.USize.toNat_toUInt16, _root_.USize.toNat_ofNatClamp_of_le hn, _root_.UInt16.toNat_ofNatLT]
  exact USize.size_sub_one_mod_uint16Size

public theorem USize.toUInt32_ofNatClamp_of_le : type_of% @_root_.USize.toUInt32_ofNatClamp_of_le := by
  intro n hn
  apply _root_.UInt32.toNat.inj
  rw [_root_.USize.toNat_toUInt32, _root_.USize.toNat_ofNatClamp_of_le hn, _root_.UInt32.toNat_ofNatLT]
  exact USize.size_sub_one_mod_uint32Size

public theorem UInt16.toUInt32_toUInt8 : type_of% @_root_.UInt16.toUInt32_toUInt8 := by
  intro a
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt8.toNat_toUInt32, _root_.UInt16.toNat_toUInt8, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 8 < 32)), _root_.UInt16.toNat_toUInt32]

public theorem UInt16.toUInt64_toUInt32 : type_of% @_root_.UInt16.toUInt64_toUInt32 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt32.toNat_toUInt64, _root_.UInt16.toNat_toUInt32, _root_.UInt16.toNat_toUInt64]

public theorem UInt16.toUInt64_toUInt8 : type_of% @_root_.UInt16.toUInt64_toUInt8 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt8.toNat_toUInt64, _root_.UInt16.toNat_toUInt8, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 8 < 64)), _root_.UInt16.toNat_toUInt64]

public theorem UInt16.toUInt8_toUInt32 : type_of% @_root_.UInt16.toUInt8_toUInt32 := by
  intro a
  apply _root_.UInt8.toNat.inj
  rw [_root_.UInt32.toNat_toUInt8, _root_.UInt16.toNat_toUInt32, _root_.UInt16.toNat_toUInt8]

public theorem UInt16.toUInt8_toUInt64 : type_of% @_root_.UInt16.toUInt8_toUInt64 := by
  intro a
  apply _root_.UInt8.toNat.inj
  rw [_root_.UInt64.toNat_toUInt8, _root_.UInt16.toNat_toUInt64, _root_.UInt16.toNat_toUInt8]

public theorem UInt32.toUInt16_toUInt64 : type_of% @_root_.UInt32.toUInt16_toUInt64 := by
  intro a
  apply _root_.UInt16.toNat.inj
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt16]

public theorem UInt32.toUInt32_toUInt16 : type_of% @_root_.UInt32.toUInt32_toUInt16 := by
  intro a
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt16.toNat_toUInt32, _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]

public theorem UInt32.toUInt64_toUInt16 : type_of% @_root_.UInt32.toUInt64_toUInt16 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt16.toNat_toUInt64, _root_.UInt32.toNat_toUInt16, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64)), _root_.UInt32.toNat_toUInt64]

public theorem UInt32.toUInt64_toUInt8 : type_of% @_root_.UInt32.toUInt64_toUInt8 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt8.toNat_toUInt64, _root_.UInt32.toNat_toUInt8, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 8 < 64)), _root_.UInt32.toNat_toUInt64]

public theorem UInt32.toUInt8_toUInt64 : type_of% @_root_.UInt32.toUInt8_toUInt64 := by
  intro a
  apply _root_.UInt8.toNat.inj
  rw [_root_.UInt64.toNat_toUInt8, _root_.UInt32.toNat_toUInt64, _root_.UInt32.toNat_toUInt8]

public theorem UInt64.toUInt32_toUInt16 : type_of% @_root_.UInt64.toUInt32_toUInt16 := by
  intro a
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt16.toNat_toUInt32, _root_.UInt64.toNat_toUInt16, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32)), _root_.UInt64.toNat_toUInt32]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))).symm

public theorem UInt64.toUInt64_toUInt16 : type_of% @_root_.UInt64.toUInt64_toUInt16 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt16.toNat_toUInt64, _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]

public theorem UInt64.toUInt64_toUInt32 : type_of% @_root_.UInt64.toUInt64_toUInt32 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt32.toNat_toUInt64, _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]

public theorem USize.toUInt32_toUInt16 : type_of% @_root_.USize.toUInt32_toUInt16 := by
  intro a
  apply _root_.UInt32.toNat.inj
  rw [_root_.UInt16.toNat_toUInt32, _root_.USize.toNat_toUInt16, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32)), _root_.USize.toNat_toUInt32]
  exact (Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))).symm

public theorem USize.toUInt64_toUInt16 : type_of% @_root_.USize.toUInt64_toUInt16 := by
  intro a
  apply _root_.UInt64.toNat.inj
  rw [_root_.UInt16.toNat_toUInt64, _root_.USize.toNat_toUInt16, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64)), _root_.USize.toNat_toUInt64]

public theorem UInt16.toUInt32_eq_mod_65536_iff : type_of% @_root_.UInt16.toUInt32_eq_mod_65536_iff := by
  intro a b
  apply _root_.UInt32.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt16.toNat_inj
  rw [_root_.UInt16.toNat_toUInt32, _root_.UInt32.toNat_mod, _root_.UInt32.toNat_toUInt16,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]

public theorem UInt32.toUInt16_eq : type_of% @_root_.UInt32.toUInt16_eq := by
  intro a b
  apply _root_.UInt16.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt32.toNat_inj
  rw [_root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_toUInt16, _root_.UInt32.toNat_mod, _root_.UInt32.toNat_mod,
    _root_.UInt32.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 32))]

public theorem UInt16.toUInt32_neg : type_of% @_root_.UInt16.toUInt32_neg := by
  intro a
  apply (UInt16.toUInt32_eq_mod_65536_iff ..).mpr
  rw [_root_.UInt32.toUInt16_neg, _root_.UInt16.toUInt16_toUInt32]

public theorem UInt16.toUInt32_sub : type_of% @_root_.UInt16.toUInt32_sub := by
  intro a b
  apply (UInt16.toUInt32_eq_mod_65536_iff ..).mpr
  rw [_root_.UInt32.toUInt16_sub, _root_.UInt16.toUInt16_toUInt32, _root_.UInt16.toUInt16_toUInt32]

public theorem UInt16.toUInt32_mod_65536 : type_of% @_root_.UInt16.toUInt32_mod_65536 := by
  intro a
  exact ((UInt16.toUInt32_eq_mod_65536_iff ..).mpr (_root_.UInt16.toUInt16_toUInt32 a).symm).symm

public theorem UInt16.toUInt64_eq_mod_65536_iff : type_of% @_root_.UInt16.toUInt64_eq_mod_65536_iff := by
  intro a b
  apply _root_.UInt64.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt16.toNat_inj
  rw [_root_.UInt16.toNat_toUInt64, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_toUInt16,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]

public theorem UInt64.toUInt16_eq : type_of% @_root_.UInt64.toUInt16_eq := by
  intro a b
  apply _root_.UInt16.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt64.toNat_inj
  rw [_root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_toUInt16, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 16 < 64))]

public theorem UInt16.toUInt64_neg : type_of% @_root_.UInt16.toUInt64_neg := by
  intro a
  apply (UInt16.toUInt64_eq_mod_65536_iff ..).mpr
  rw [_root_.UInt64.toUInt16_neg, _root_.UInt16.toUInt16_toUInt64]

public theorem UInt16.toUInt64_sub : type_of% @_root_.UInt16.toUInt64_sub := by
  intro a b
  apply (UInt16.toUInt64_eq_mod_65536_iff ..).mpr
  rw [_root_.UInt64.toUInt16_sub, _root_.UInt16.toUInt16_toUInt64, _root_.UInt16.toUInt16_toUInt64]

public theorem UInt16.toUInt64_mod_65536 : type_of% @_root_.UInt16.toUInt64_mod_65536 := by
  intro a
  exact ((UInt16.toUInt64_eq_mod_65536_iff ..).mpr (_root_.UInt16.toUInt16_toUInt64 a).symm).symm

public theorem UInt32.toUInt64_eq_mod_4294967296_iff : type_of% @_root_.UInt32.toUInt64_eq_mod_4294967296_iff := by
  intro a b
  apply _root_.UInt64.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt32.toNat_inj
  rw [_root_.UInt32.toNat_toUInt64, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_toUInt32,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]

public theorem UInt64.toUInt32_eq : type_of% @_root_.UInt64.toUInt32_eq := by
  intro a b
  apply _root_.UInt32.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt64.toNat_inj
  rw [_root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_toUInt32, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))]

public theorem UInt32.toUInt64_neg : type_of% @_root_.UInt32.toUInt64_neg := by
  intro a
  apply (UInt32.toUInt64_eq_mod_4294967296_iff ..).mpr
  rw [_root_.UInt64.toUInt32_neg, _root_.UInt32.toUInt32_toUInt64]

public theorem UInt32.toUInt64_sub : type_of% @_root_.UInt32.toUInt64_sub := by
  intro a b
  apply (UInt32.toUInt64_eq_mod_4294967296_iff ..).mpr
  rw [_root_.UInt64.toUInt32_sub, _root_.UInt32.toUInt32_toUInt64, _root_.UInt32.toUInt32_toUInt64]

public theorem UInt32.toUInt64_mod_4294967296 : type_of% @_root_.UInt32.toUInt64_mod_4294967296 := by
  intro a
  exact ((UInt32.toUInt64_eq_mod_4294967296_iff ..).mpr (_root_.UInt32.toUInt32_toUInt64 a).symm).symm

public theorem UInt16.lt_add_one : type_of% @_root_.UInt16.lt_add_one := by
  intro a h
  apply _root_.UInt16.lt_iff_toBitVec_lt.mpr
  rw [_root_.UInt16.toBitVec_add, _root_.UInt16.toBitVec_one]
  apply _root_.BitVec.lt_add_one
  intro e
  apply h
  apply _root_.UInt16.toBitVec_inj.mp
  rw [_root_.UInt16.toBitVec_neg, _root_.UInt16.toBitVec_one, _root_.BitVec.neg_one_eq_allOnes]
  exact e

public theorem UInt32.lt_add_one : type_of% @_root_.UInt32.lt_add_one := by
  intro a h
  apply _root_.UInt32.lt_iff_toBitVec_lt.mpr
  rw [_root_.UInt32.toBitVec_add, _root_.UInt32.toBitVec_one]
  apply _root_.BitVec.lt_add_one
  intro e
  apply h
  apply _root_.UInt32.toBitVec_inj.mp
  rw [_root_.UInt32.toBitVec_neg, _root_.UInt32.toBitVec_one, _root_.BitVec.neg_one_eq_allOnes]
  exact e

public theorem UInt64.lt_add_one : type_of% @_root_.UInt64.lt_add_one := by
  intro a h
  apply _root_.UInt64.lt_iff_toBitVec_lt.mpr
  rw [_root_.UInt64.toBitVec_add, _root_.UInt64.toBitVec_one]
  apply _root_.BitVec.lt_add_one
  intro e
  apply h
  apply _root_.UInt64.toBitVec_inj.mp
  rw [_root_.UInt64.toBitVec_neg, _root_.UInt64.toBitVec_one, _root_.BitVec.neg_one_eq_allOnes]
  exact e

private theorem mod_reduced_width {a small big : Nat} (ha : a < big) (h : small ≤ big) :
    a % (small % big) = a % small := by
  by_cases same : small = big
  · subst small
    rw [Nat.mod_self, Nat.mod_zero, Nat.mod_eq_of_lt ha]
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne h same)]

public theorem UInt32.toUSize_eq_mod_4294967296_iff : type_of% @_root_.UInt32.toUSize_eq_mod_4294967296_iff := by
  intro a b
  apply _root_.USize.toNat_inj.symm.trans
  apply Iff.trans _ _root_.UInt32.toNat_inj
  rw [_root_.UInt32.toNat_toUSize, _root_.USize.toNat_mod, _root_.USize.toNat_toUInt32,
    _root_.USize.toNat_ofNat, mod_reduced_width b.toNat_lt_size _root_.UInt32.size_le_usizeSize]

public theorem USize.toUInt64_eq_mod_usizeSize_iff : type_of% @_root_.USize.toUInt64_eq_mod_usizeSize_iff := by
  intro a b
  apply _root_.UInt64.toNat_inj.symm.trans
  apply Iff.trans _ _root_.USize.toNat_inj
  rw [_root_.USize.toNat_toUInt64, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_toUSize,
    _root_.UInt64.toNat_ofNat', mod_reduced_width b.toNat_lt_size _root_.USize.size_le_uint64Size]

public theorem UInt32.toUSize_add : type_of% @_root_.UInt32.toUSize_add := by
  intro a b
  apply (UInt32.toUSize_eq_mod_4294967296_iff ..).mpr
  rw [_root_.USize.toUInt32_add, _root_.UInt32.toUInt32_toUSize, _root_.UInt32.toUInt32_toUSize]

public theorem UInt32.toUSize_mul : type_of% @_root_.UInt32.toUSize_mul := by
  intro a b
  apply (UInt32.toUSize_eq_mod_4294967296_iff ..).mpr
  rw [_root_.USize.toUInt32_mul, _root_.UInt32.toUInt32_toUSize, _root_.UInt32.toUInt32_toUSize]

public theorem UInt32.toUSize_sub : type_of% @_root_.UInt32.toUSize_sub := by
  intro a b
  apply (UInt32.toUSize_eq_mod_4294967296_iff ..).mpr
  rw [_root_.USize.toUInt32_sub, _root_.UInt32.toUInt32_toUSize, _root_.UInt32.toUInt32_toUSize]

public theorem USize.toUInt64_sub : type_of% @_root_.USize.toUInt64_sub := by
  intro a b
  apply (USize.toUInt64_eq_mod_usizeSize_iff ..).mpr
  rw [_root_.UInt64.toUSize_sub, _root_.USize.toUSize_toUInt64, _root_.USize.toUSize_toUInt64]

public theorem UInt32.toUSize_neg : type_of% @_root_.UInt32.toUSize_neg := by
  intro a
  apply (UInt32.toUSize_eq_mod_4294967296_iff ..).mpr
  rw [_root_.USize.toUInt32_neg, _root_.UInt32.toUInt32_toUSize]

public theorem USize.toUInt64_neg : type_of% @_root_.USize.toUInt64_neg := by
  intro a
  apply (USize.toUInt64_eq_mod_usizeSize_iff ..).mpr
  rw [_root_.UInt64.toUSize_neg, _root_.USize.toUSize_toUInt64]

public theorem USize.toUInt32_eq : type_of% @_root_.USize.toUInt32_eq := by
  intro a b
  apply _root_.UInt32.toNat_inj.symm.trans
  apply Iff.trans _ _root_.USize.toNat_inj
  rw [_root_.USize.toNat_toUInt32, _root_.USize.toNat_toUInt32, _root_.USize.toNat_mod, _root_.USize.toNat_mod,
    _root_.USize.toNat_ofNat, mod_reduced_width a.toNat_lt_size _root_.UInt32.size_le_usizeSize,
    mod_reduced_width b.toNat_lt_size _root_.UInt32.size_le_usizeSize]

public theorem UInt64.toUSize_lt : type_of% @_root_.UInt64.toUSize_lt := by
  intro a b
  apply _root_.USize.lt_iff_toNat_lt.trans
  apply Iff.trans _ _root_.UInt64.lt_iff_toNat_lt.symm
  rw [_root_.UInt64.toNat_toUSize, _root_.UInt64.toNat_toUSize, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat', mod_reduced_width a.toNat_lt_size _root_.USize.size_le_uint64Size,
    mod_reduced_width b.toNat_lt_size _root_.USize.size_le_uint64Size]

public theorem UInt64.toUSize_le : type_of% @_root_.UInt64.toUSize_le := by
  intro a b
  apply _root_.USize.le_iff_toNat_le.trans
  apply Iff.trans _ _root_.UInt64.le_iff_toNat_le.symm
  rw [_root_.UInt64.toNat_toUSize, _root_.UInt64.toNat_toUSize, _root_.UInt64.toNat_mod, _root_.UInt64.toNat_mod,
    _root_.UInt64.toNat_ofNat', mod_reduced_width a.toNat_lt_size _root_.USize.size_le_uint64Size,
    mod_reduced_width b.toNat_lt_size _root_.USize.size_le_uint64Size]

public theorem UInt16.ofNat_usizeSize_sub_one : type_of% @_root_.UInt16.ofNat_usizeSize_sub_one := by
  apply Eq.trans _ _root_.UInt16.neg_one_eq
  apply _root_.UInt16.toNat.inj
  exact _root_.UInt16.toNat_ofNat'.trans (USize.size_sub_one_mod_uint16Size.trans toNat_neg_one_16.symm)

public theorem UInt32.ofNat_usizeSize_sub_one : type_of% @_root_.UInt32.ofNat_usizeSize_sub_one := by
  apply Eq.trans _ _root_.UInt32.neg_one_eq
  apply _root_.UInt32.toNat.inj
  exact _root_.UInt32.toNat_ofNat'.trans (USize.size_sub_one_mod_uint32Size.trans toNat_neg_one_32.symm)

public theorem USize.toUInt32_mod : type_of% @_root_.USize.toUInt32_mod := by
  intro a b ha hb
  have below (z : USize) (h : z < 4294967296) : z.toNat < 2^32 := by
    have small := _root_.USize.lt_iff_toNat_lt.mp h
    rw [_root_.USize.toNat_ofNat] at small
    exact Nat.lt_of_lt_of_le small (Nat.mod_le ..)
  apply _root_.UInt32.toNat.inj
  rw [_root_.USize.toNat_toUInt32, _root_.USize.toNat_mod, _root_.UInt32.toNat_mod,
    _root_.USize.toNat_toUInt32, _root_.USize.toNat_toUInt32]
  exact Nat.mod_mod_eq_mod_mod_mod (below a ha) (below b hb)

end OmegaChecks.InitPort.Alternatives
