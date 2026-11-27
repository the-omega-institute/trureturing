module

import all Init.Data.SInt.Lemmas

public import OmegaChecks.InitPort.Alternatives.Word.Signed

namespace OmegaChecks.InitPort.Alternatives

public theorem Int16.ofIntLE_int8ToInt._proof_1 : type_of% @_root_.Int16.ofIntLE_int8ToInt._proof_1 := by
  rw [_root_.Int16.toInt_minValue, _root_.Int8.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 15)))

public theorem Int16.ofIntLE_int8ToInt._proof_2 : type_of% @_root_.Int16.ofIntLE_int8ToInt._proof_2 := by
  rw [_root_.Int8.toInt_maxValue, _root_.Int16.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 15))) 1

public theorem Int32.ofIntLE_int8ToInt._proof_1 : type_of% @_root_.Int32.ofIntLE_int8ToInt._proof_1 := by
  rw [_root_.Int32.toInt_minValue, _root_.Int8.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 31)))

public theorem Int32.ofIntLE_int8ToInt._proof_2 : type_of% @_root_.Int32.ofIntLE_int8ToInt._proof_2 := by
  rw [_root_.Int8.toInt_maxValue, _root_.Int32.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 31))) 1

public theorem Int64.ofIntLE_int8ToInt._proof_1 : type_of% @_root_.Int64.ofIntLE_int8ToInt._proof_1 := by
  rw [_root_.Int64.toInt_minValue, _root_.Int8.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 63)))

public theorem Int64.ofIntLE_int8ToInt._proof_2 : type_of% @_root_.Int64.ofIntLE_int8ToInt._proof_2 := by
  rw [_root_.Int8.toInt_maxValue, _root_.Int64.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 7 ≤ 63))) 1

public theorem Int32.ofIntLE_int16ToInt._proof_1 : type_of% @_root_.Int32.ofIntLE_int16ToInt._proof_1 := by
  rw [_root_.Int32.toInt_minValue, _root_.Int16.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 31)))

public theorem Int32.ofIntLE_int16ToInt._proof_2 : type_of% @_root_.Int32.ofIntLE_int16ToInt._proof_2 := by
  rw [_root_.Int16.toInt_maxValue, _root_.Int32.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 31))) 1

public theorem Int64.ofIntLE_int16ToInt._proof_1 : type_of% @_root_.Int64.ofIntLE_int16ToInt._proof_1 := by
  rw [_root_.Int64.toInt_minValue, _root_.Int16.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 63)))

public theorem Int64.ofIntLE_int16ToInt._proof_2 : type_of% @_root_.Int64.ofIntLE_int16ToInt._proof_2 := by
  rw [_root_.Int16.toInt_maxValue, _root_.Int64.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 63))) 1

public theorem Int64.ofIntLE_int32ToInt._proof_1 : type_of% @_root_.Int64.ofIntLE_int32ToInt._proof_1 := by
  rw [_root_.Int64.toInt_minValue, _root_.Int32.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 31 ≤ 63)))

public theorem Int64.ofIntLE_int32ToInt._proof_2 : type_of% @_root_.Int64.ofIntLE_int32ToInt._proof_2 := by
  rw [_root_.Int32.toInt_maxValue, _root_.Int64.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 31 ≤ 63))) 1

public theorem Int16.ofIntLE_bitVecToInt._proof_1 : type_of% @_root_.Int16.ofIntLE_bitVecToInt._proof_1 := by
  intro n
  rw [_root_.Int16.toInt_minValue]
  exact _root_.BitVec.le_toInt n

public theorem Int16.ofIntLE_bitVecToInt._proof_2 : type_of% @_root_.Int16.ofIntLE_bitVecToInt._proof_2 := by
  intro n
  rw [_root_.Int16.toInt_maxValue]
  exact Int.le_sub_one_of_lt (@_root_.BitVec.toInt_lt _ n)

public theorem Int32.ofIntLE_bitVecToInt._proof_1 : type_of% @_root_.Int32.ofIntLE_bitVecToInt._proof_1 := by
  intro n
  rw [_root_.Int32.toInt_minValue]
  exact _root_.BitVec.le_toInt n

public theorem Int32.ofIntLE_bitVecToInt._proof_2 : type_of% @_root_.Int32.ofIntLE_bitVecToInt._proof_2 := by
  intro n
  rw [_root_.Int32.toInt_maxValue]
  exact Int.le_sub_one_of_lt (@_root_.BitVec.toInt_lt _ n)

public theorem Int64.ofIntLE_bitVecToInt._proof_1 : type_of% @_root_.Int64.ofIntLE_bitVecToInt._proof_1 := by
  intro n
  rw [_root_.Int64.toInt_minValue]
  exact _root_.BitVec.le_toInt n

public theorem Int64.ofIntLE_bitVecToInt._proof_2 : type_of% @_root_.Int64.ofIntLE_bitVecToInt._proof_2 := by
  intro n
  rw [_root_.Int64.toInt_maxValue]
  exact Int.le_sub_one_of_lt (@_root_.BitVec.toInt_lt _ n)

public theorem Int16.toInt8_ofInt : type_of% @_root_.Int16.toInt8_ofInt := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int16.toInt_toInt8, _root_.Int16.toInt_ofInt, _root_.Int8.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 16))

public theorem Int8.toInt16_ofIntLE : type_of% @_root_.Int8.toInt16_ofIntLE := by
  intro n lo hi
  apply _root_.Int16.toInt.inj
  rw [_root_.Int8.toInt_toInt16, _root_.Int8.toInt_ofIntLE, _root_.Int16.toInt_ofIntLE]

public theorem Int8.toInt16_ofInt : type_of% @_root_.Int8.toInt16_ofInt := by
  intro n lo hi
  exact Int8.toInt16_ofIntLE lo hi

public theorem Int8.toInt16_ne_minValue : type_of% @_root_.Int8.toInt16_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int16.toInt e
  rw [_root_.Int8.toInt_toInt16, _root_.Int16.toInt_minValue] at eq
  have bound : (2 : Int)^7 < 2^15 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 15))
  exact Int.not_lt_of_ge (_root_.Int8.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int32.toInt8_ofInt : type_of% @_root_.Int32.toInt8_ofInt := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int32.toInt_toInt8, _root_.Int32.toInt_ofInt, _root_.Int8.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 32))

public theorem Int8.toInt32_ofIntLE : type_of% @_root_.Int8.toInt32_ofIntLE := by
  intro n lo hi
  apply _root_.Int32.toInt.inj
  rw [_root_.Int8.toInt_toInt32, _root_.Int8.toInt_ofIntLE, _root_.Int32.toInt_ofIntLE]

public theorem Int8.toInt32_ofInt : type_of% @_root_.Int8.toInt32_ofInt := by
  intro n lo hi
  exact Int8.toInt32_ofIntLE lo hi

public theorem Int8.toInt32_ne_minValue : type_of% @_root_.Int8.toInt32_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int32.toInt e
  rw [_root_.Int8.toInt_toInt32, _root_.Int32.toInt_minValue] at eq
  have bound : (2 : Int)^7 < 2^31 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 31))
  exact Int.not_lt_of_ge (_root_.Int8.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int64.toInt8_ofInt : type_of% @_root_.Int64.toInt8_ofInt := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int64.toInt_toInt8, _root_.Int64.toInt_ofInt, _root_.Int8.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 64))

public theorem Int8.toInt64_ofIntLE : type_of% @_root_.Int8.toInt64_ofIntLE := by
  intro n lo hi
  apply _root_.Int64.toInt.inj
  rw [_root_.Int8.toInt_toInt64, _root_.Int8.toInt_ofIntLE, _root_.Int64.toInt_ofIntLE]

public theorem Int8.toInt64_ofInt : type_of% @_root_.Int8.toInt64_ofInt := by
  intro n lo hi
  exact Int8.toInt64_ofIntLE lo hi

public theorem Int8.toInt64_ne_minValue : type_of% @_root_.Int8.toInt64_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int64.toInt e
  rw [_root_.Int8.toInt_toInt64, _root_.Int64.toInt_minValue] at eq
  have bound : (2 : Int)^7 < 2^63 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 63))
  exact Int.not_lt_of_ge (_root_.Int8.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int32.toInt16_ofInt : type_of% @_root_.Int32.toInt16_ofInt := by
  intro n
  apply _root_.Int16.toInt.inj
  rw [_root_.Int32.toInt_toInt16, _root_.Int32.toInt_ofInt, _root_.Int16.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))

public theorem Int16.toInt32_ofIntLE : type_of% @_root_.Int16.toInt32_ofIntLE := by
  intro n lo hi
  apply _root_.Int32.toInt.inj
  rw [_root_.Int16.toInt_toInt32, _root_.Int16.toInt_ofIntLE, _root_.Int32.toInt_ofIntLE]

public theorem Int16.toInt32_ofInt : type_of% @_root_.Int16.toInt32_ofInt := by
  intro n lo hi
  exact Int16.toInt32_ofIntLE lo hi

public theorem Int16.toInt32_ne_minValue : type_of% @_root_.Int16.toInt32_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int32.toInt e
  rw [_root_.Int16.toInt_toInt32, _root_.Int32.toInt_minValue] at eq
  have bound : (2 : Int)^15 < 2^31 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 31))
  exact Int.not_lt_of_ge (_root_.Int16.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int64.toInt16_ofInt : type_of% @_root_.Int64.toInt16_ofInt := by
  intro n
  apply _root_.Int16.toInt.inj
  rw [_root_.Int64.toInt_toInt16, _root_.Int64.toInt_ofInt, _root_.Int16.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 64))

public theorem Int16.toInt64_ofIntLE : type_of% @_root_.Int16.toInt64_ofIntLE := by
  intro n lo hi
  apply _root_.Int64.toInt.inj
  rw [_root_.Int16.toInt_toInt64, _root_.Int16.toInt_ofIntLE, _root_.Int64.toInt_ofIntLE]

public theorem Int16.toInt64_ofInt : type_of% @_root_.Int16.toInt64_ofInt := by
  intro n lo hi
  exact Int16.toInt64_ofIntLE lo hi

public theorem Int16.toInt64_ne_minValue : type_of% @_root_.Int16.toInt64_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int64.toInt e
  rw [_root_.Int16.toInt_toInt64, _root_.Int64.toInt_minValue] at eq
  have bound : (2 : Int)^15 < 2^63 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 63))
  exact Int.not_lt_of_ge (_root_.Int16.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int64.toInt32_ofInt : type_of% @_root_.Int64.toInt32_ofInt := by
  intro n
  apply _root_.Int32.toInt.inj
  rw [_root_.Int64.toInt_toInt32, _root_.Int64.toInt_ofInt, _root_.Int32.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 32 ≤ 64))

public theorem Int32.toInt64_ofIntLE : type_of% @_root_.Int32.toInt64_ofIntLE := by
  intro n lo hi
  apply _root_.Int64.toInt.inj
  rw [_root_.Int32.toInt_toInt64, _root_.Int32.toInt_ofIntLE, _root_.Int64.toInt_ofIntLE]

public theorem Int32.toInt64_ofInt : type_of% @_root_.Int32.toInt64_ofInt := by
  intro n lo hi
  exact Int32.toInt64_ofIntLE lo hi

public theorem Int32.toInt64_ne_minValue : type_of% @_root_.Int32.toInt64_ne_minValue := by
  intro a e
  have eq := congrArg _root_.Int64.toInt e
  rw [_root_.Int32.toInt_toInt64, _root_.Int64.toInt_minValue] at eq
  have bound : (2 : Int)^31 < 2^63 := Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 31 < 63))
  exact Int.not_lt_of_ge (_root_.Int32.le_toInt a) (eq ▸ Int.neg_lt_neg bound)

public theorem Int16.ofIntClamp_bitVecToInt : type_of% @_root_.Int16.ofIntClamp_bitVecToInt := by
  intro n
  rw [← _root_.Int16.ofIntLE_eq_ofIntClamp
    (h₁ := Int16.ofIntLE_bitVecToInt._proof_1 n) (h₂ := Int16.ofIntLE_bitVecToInt._proof_2 n)]
  exact _root_.Int16.ofIntLE_bitVecToInt n

public theorem Int32.ofIntClamp_bitVecToInt : type_of% @_root_.Int32.ofIntClamp_bitVecToInt := by
  intro n
  rw [← _root_.Int32.ofIntLE_eq_ofIntClamp
    (h₁ := Int32.ofIntLE_bitVecToInt._proof_1 n) (h₂ := Int32.ofIntLE_bitVecToInt._proof_2 n)]
  exact _root_.Int32.ofIntLE_bitVecToInt n

public theorem Int64.ofIntClamp_bitVecToInt : type_of% @_root_.Int64.ofIntClamp_bitVecToInt := by
  intro n
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp
    (h₁ := Int64.ofIntLE_bitVecToInt._proof_1 n) (h₂ := Int64.ofIntLE_bitVecToInt._proof_2 n)]
  exact _root_.Int64.ofIntLE_bitVecToInt n

public theorem Int16.ofIntClamp_int8ToInt : type_of% @_root_.Int16.ofIntClamp_int8ToInt := by
  intro n
  rw [← _root_.Int16.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int16.ofIntLE_int8ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int16.ofIntLE_int8ToInt._proof_2)]
  exact _root_.Int16.ofIntLE_int8ToInt n

public theorem Int32.ofIntClamp_int8ToInt : type_of% @_root_.Int32.ofIntClamp_int8ToInt := by
  intro n
  rw [← _root_.Int32.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int32.ofIntLE_int8ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int32.ofIntLE_int8ToInt._proof_2)]
  exact _root_.Int32.ofIntLE_int8ToInt n

public theorem Int64.ofIntClamp_int8ToInt : type_of% @_root_.Int64.ofIntClamp_int8ToInt := by
  intro n
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int64.ofIntLE_int8ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int64.ofIntLE_int8ToInt._proof_2)]
  exact _root_.Int64.ofIntLE_int8ToInt n

public theorem Int32.ofIntClamp_int16ToInt : type_of% @_root_.Int32.ofIntClamp_int16ToInt := by
  intro n
  rw [← _root_.Int32.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int32.ofIntLE_int16ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int32.ofIntLE_int16ToInt._proof_2)]
  exact _root_.Int32.ofIntLE_int16ToInt n

public theorem Int64.ofIntClamp_int16ToInt : type_of% @_root_.Int64.ofIntClamp_int16ToInt := by
  intro n
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int64.ofIntLE_int16ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int64.ofIntLE_int16ToInt._proof_2)]
  exact _root_.Int64.ofIntLE_int16ToInt n

public theorem Int64.ofIntClamp_int32ToInt : type_of% @_root_.Int64.ofIntClamp_int32ToInt := by
  intro n
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp
    (h₁ := Int.le_trans Int64.ofIntLE_int32ToInt._proof_1 n.minValue_le_toInt)
    (h₂ := Int.le_trans n.toInt_le Int64.ofIntLE_int32ToInt._proof_2)]
  exact _root_.Int64.ofIntLE_int32ToInt n

public theorem Int16.toInt8_ofIntClamp : type_of% @_root_.Int16.toInt8_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int16.minValue.toInt ≤ n := _root_.Int16.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int16.maxValue.toInt := _root_.Int16.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int16.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int16.toInt8_ofIntLE lower upper

public theorem Int32.toInt8_ofIntClamp : type_of% @_root_.Int32.toInt8_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int32.minValue.toInt ≤ n := _root_.Int32.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int32.maxValue.toInt := _root_.Int32.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int32.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int32.toInt8_ofIntLE lower upper

public theorem Int64.toInt8_ofIntClamp : type_of% @_root_.Int64.toInt8_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int64.minValue.toInt ≤ n := _root_.Int64.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int64.maxValue.toInt := _root_.Int64.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int64.toInt8_ofIntLE lower upper

public theorem Int32.toInt16_ofIntClamp : type_of% @_root_.Int32.toInt16_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int32.minValue.toInt ≤ n := _root_.Int32.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int32.maxValue.toInt := _root_.Int32.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int32.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int32.toInt16_ofIntLE lower upper

public theorem Int64.toInt16_ofIntClamp : type_of% @_root_.Int64.toInt16_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int64.minValue.toInt ≤ n := _root_.Int64.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int64.maxValue.toInt := _root_.Int64.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int64.toInt16_ofIntLE lower upper

public theorem Int64.toInt32_ofIntClamp : type_of% @_root_.Int64.toInt32_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int64.minValue.toInt ≤ n := _root_.Int64.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int64.maxValue.toInt := _root_.Int64.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int64.toInt32_ofIntLE lower upper

public theorem Int64.toISize_ofIntClamp : type_of% @_root_.Int64.toISize_ofIntClamp := by
  intro n lo hi
  have lower : _root_.Int64.minValue.toInt ≤ n := _root_.Int64.toInt_minValue ▸ lo
  have upper : n ≤ _root_.Int64.maxValue.toInt := _root_.Int64.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  rw [← _root_.Int64.ofIntLE_eq_ofIntClamp (h₁ := lower) (h₂ := upper)]
  exact _root_.Int64.toISize_ofIntLE lower upper

public theorem Int16.toNatClampNeg_ofNat_of_lt : type_of% @_root_.Int16.toNatClampNeg_ofNat_of_lt := by
  intro n h
  exact congrArg Int.toNat (_root_.Int16.toInt_ofNat_of_lt h)

public theorem Int16.minValue_le : type_of% @_root_.Int16.minValue_le := by
  intro n
  exact _root_.Int16.le_iff_toInt_le.mpr n.minValue_le_toInt

public theorem Int16.ofNat_div : type_of% @_root_.Int16.ofNat_div := by
  intro a b ha hb
  rw [← _root_.Int16.ofInt_eq_ofNat, ← _root_.Int16.ofInt_eq_ofNat, ← _root_.Int16.ofInt_eq_ofNat,
    Int.ofNat_tdiv]
  apply _root_.Int16.ofInt_tdiv
  · exact Int.le_trans (Int.le_of_lt _root_.Int16.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int16.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int16.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int16.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int16.ofNat_mod : type_of% @_root_.Int16.ofNat_mod := by
  intro a b ha hb
  rw [← _root_.Int16.ofInt_eq_ofNat, ← _root_.Int16.ofInt_eq_ofNat, ← _root_.Int16.ofInt_eq_ofNat,
    Int.ofNat_tmod]
  apply _root_.Int16.ofInt_tmod
  · exact Int.le_trans (Int.le_of_lt _root_.Int16.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int16.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int16.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int16.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int16.toNatClampNeg_ofIntClamp_of_lt : type_of% @_root_.Int16.toNatClampNeg_ofIntClamp_of_lt := by
  intro n hi
  have upper : n ≤ _root_.Int16.maxValue.toInt := _root_.Int16.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  if lower : _root_.Int16.minValue.toInt ≤ n then
    exact congrArg Int.toNat (_root_.Int16.toInt_ofIntClamp lower upper)
  else
    rw [_root_.Int16.ofIntClamp, dite_eq_right lower, _root_.Int16.toNatClampNeg_minValue]
    exact (Int.toNat_eq_zero.mpr (Int.le_of_lt (Int.lt_trans (Int.lt_of_not_ge lower)
      _root_.Int16.toInt_minValue_lt_zero))).symm

public theorem Int32.toNatClampNeg_ofNat_of_lt : type_of% @_root_.Int32.toNatClampNeg_ofNat_of_lt := by
  intro n h
  exact congrArg Int.toNat (_root_.Int32.toInt_ofNat_of_lt h)

public theorem Int32.minValue_le : type_of% @_root_.Int32.minValue_le := by
  intro n
  exact _root_.Int32.le_iff_toInt_le.mpr n.minValue_le_toInt

public theorem Int32.ofNat_div : type_of% @_root_.Int32.ofNat_div := by
  intro a b ha hb
  rw [← _root_.Int32.ofInt_eq_ofNat, ← _root_.Int32.ofInt_eq_ofNat, ← _root_.Int32.ofInt_eq_ofNat,
    Int.ofNat_tdiv]
  apply _root_.Int32.ofInt_tdiv
  · exact Int.le_trans (Int.le_of_lt _root_.Int32.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int32.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int32.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int32.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int32.ofNat_mod : type_of% @_root_.Int32.ofNat_mod := by
  intro a b ha hb
  rw [← _root_.Int32.ofInt_eq_ofNat, ← _root_.Int32.ofInt_eq_ofNat, ← _root_.Int32.ofInt_eq_ofNat,
    Int.ofNat_tmod]
  apply _root_.Int32.ofInt_tmod
  · exact Int.le_trans (Int.le_of_lt _root_.Int32.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int32.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int32.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int32.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int32.toNatClampNeg_ofIntClamp_of_lt : type_of% @_root_.Int32.toNatClampNeg_ofIntClamp_of_lt := by
  intro n hi
  have upper : n ≤ _root_.Int32.maxValue.toInt := _root_.Int32.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  if lower : _root_.Int32.minValue.toInt ≤ n then
    exact congrArg Int.toNat (_root_.Int32.toInt_ofIntClamp lower upper)
  else
    rw [_root_.Int32.ofIntClamp, dite_eq_right lower, _root_.Int32.toNatClampNeg_minValue]
    exact (Int.toNat_eq_zero.mpr (Int.le_of_lt (Int.lt_trans (Int.lt_of_not_ge lower)
      _root_.Int32.toInt_minValue_lt_zero))).symm

public theorem Int64.toNatClampNeg_ofNat_of_lt : type_of% @_root_.Int64.toNatClampNeg_ofNat_of_lt := by
  intro n h
  exact congrArg Int.toNat (_root_.Int64.toInt_ofNat_of_lt h)

public theorem Int64.minValue_le : type_of% @_root_.Int64.minValue_le := by
  intro n
  exact _root_.Int64.le_iff_toInt_le.mpr n.minValue_le_toInt

public theorem Int64.ofNat_div : type_of% @_root_.Int64.ofNat_div := by
  intro a b ha hb
  rw [← _root_.Int64.ofInt_eq_ofNat, ← _root_.Int64.ofInt_eq_ofNat, ← _root_.Int64.ofInt_eq_ofNat,
    Int.ofNat_tdiv]
  apply _root_.Int64.ofInt_tdiv
  · exact Int.le_trans (Int.le_of_lt _root_.Int64.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int64.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int64.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int64.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int64.ofNat_mod : type_of% @_root_.Int64.ofNat_mod := by
  intro a b ha hb
  rw [← _root_.Int64.ofInt_eq_ofNat, ← _root_.Int64.ofInt_eq_ofNat, ← _root_.Int64.ofInt_eq_ofNat,
    Int.ofNat_tmod]
  apply _root_.Int64.ofInt_tmod
  · exact Int.le_trans (Int.le_of_lt _root_.Int64.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int64.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr ha)
  · exact Int.le_trans (Int.le_of_lt _root_.Int64.toInt_minValue_lt_zero) (Int.natCast_nonneg _)
  · rw [_root_.Int64.toInt_maxValue]
    exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr hb)

public theorem Int64.toNatClampNeg_ofIntClamp_of_lt : type_of% @_root_.Int64.toNatClampNeg_ofIntClamp_of_lt := by
  intro n hi
  have upper : n ≤ _root_.Int64.maxValue.toInt := _root_.Int64.toInt_maxValue ▸ Int.le_sub_one_of_lt hi
  if lower : _root_.Int64.minValue.toInt ≤ n then
    exact congrArg Int.toNat (_root_.Int64.toInt_ofIntClamp lower upper)
  else
    rw [_root_.Int64.ofIntClamp, dite_eq_right lower, _root_.Int64.toNatClampNeg_minValue]
    exact (Int.toNat_eq_zero.mpr (Int.le_of_lt (Int.lt_trans (Int.lt_of_not_ge lower)
      _root_.Int64.toInt_minValue_lt_zero))).symm

public theorem ISize.toNatClampNeg_ofNat_of_lt : type_of% @_root_.ISize.toNatClampNeg_ofNat_of_lt := by
  intro n h
  exact congrArg Int.toNat (_root_.ISize.toInt_ofNat_of_lt h)

public theorem ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits : type_of% @_root_.ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits := by
  intro n h
  exact congrArg Int.toNat (_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits h)

public theorem ISize.toNatClampNeg_one : type_of% @_root_.ISize.toNatClampNeg_one := by
  exact congrArg Int.toNat _root_.ISize.toInt_one

public theorem Int8.toISize_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int8.toISize_ne_minValue._proof_1_2) :=
  fun _ lower upper eq => Int.not_lt_of_ge (eq ▸ lower) (Int.lt_of_le_of_lt upper
    (Int.neg_lt_neg (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 31)))))

public theorem Int8.toInt16_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int8.toInt16_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 15))))

public theorem Int8.toInt32_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int8.toInt32_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 31))))

public theorem Int8.toInt64_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int8.toInt64_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 63))))

public theorem Int16.toISize_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int16.toISize_ne_minValue._proof_1_2) :=
  fun _ lower upper eq => Int.not_lt_of_ge (eq ▸ lower) (Int.lt_of_le_of_lt upper
    (Int.neg_lt_neg (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 31)))))

public theorem Int16.toISize_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.Int16.toISize_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr
    (Nat.lt_of_le_of_lt h (show 32767 < 2 ^ 15 from by decide))))

public theorem Int16.toInt32_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int16.toInt32_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 31))))

public theorem Int16.toInt32_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.Int16.toInt32_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr
    (Nat.lt_of_le_of_lt h (show 32767 < 2 ^ 15 from by decide))))

public theorem Int16.toInt64_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int16.toInt64_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 63))))

public theorem Int16.toInt64_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.Int16.toInt64_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr
    (Nat.lt_of_le_of_lt h (show 32767 < 2 ^ 15 from by decide))))

public theorem Int16.toInt_ofNat_of_lt._proof_1_1 :
    type_of% (private_decl% @_root_.Int16.toInt_ofNat_of_lt._proof_1_1) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 15))) (Int.natCast_nonneg _))

public theorem Int16.toInt_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int16.toInt_ofNat_of_lt._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem Int16.toNatClampNeg_ofIntClamp_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int16.toNatClampNeg_ofIntClamp_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt h)

public theorem Int16.toNatClampNeg_ofIntClamp_of_lt._proof_1_4 :
    type_of% (private_decl% @_root_.Int16.toNatClampNeg_ofIntClamp_of_lt._proof_1_4) :=
  fun negative positive => negative (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 15))) (Int.le_of_lt (Int.lt_of_not_ge positive)))

public theorem Int16.toNatClampNeg_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int16.toNatClampNeg_ofNat_of_lt._proof_1_2) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 15))) (Int.natCast_nonneg _))

public theorem Int16.toNatClampNeg_ofNat_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int16.toNatClampNeg_ofNat_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem Int32.toISize_ne_minValue._proof_1_3 :
    type_of% (private_decl% @_root_.Int32.toISize_ne_minValue._proof_1_3) :=
  fun _ lower minimum distinct eq => distinct (Int.le_antisymm (eq ▸ minimum) lower)

public theorem Int32.toISize_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.Int32.toISize_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr
    (Nat.lt_of_le_of_lt h (show 2147483647 < 2 ^ 31 from by decide))))

public theorem Int32.toInt64_ne_minValue._proof_1_2 :
    type_of% (private_decl% @_root_.Int32.toInt64_ne_minValue._proof_1_2) :=
  fun _ lower eq => Int.not_lt_of_ge (eq ▸ lower) (Int.neg_lt_neg
    (Int.ofNat_lt.mpr (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 31 < 63))))

public theorem Int32.toInt64_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.Int32.toInt64_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr
    (Nat.lt_of_le_of_lt h (show 2147483647 < 2 ^ 31 from by decide))))

public theorem Int32.toInt_ofNat_of_lt._proof_1_1 :
    type_of% (private_decl% @_root_.Int32.toInt_ofNat_of_lt._proof_1_1) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 31))) (Int.natCast_nonneg _))

public theorem Int32.toInt_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int32.toInt_ofNat_of_lt._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem Int32.toNatClampNeg_ofIntClamp_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int32.toNatClampNeg_ofIntClamp_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt h)

public theorem Int32.toNatClampNeg_ofIntClamp_of_lt._proof_1_4 :
    type_of% (private_decl% @_root_.Int32.toNatClampNeg_ofIntClamp_of_lt._proof_1_4) :=
  fun negative positive => negative (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 31))) (Int.le_of_lt (Int.lt_of_not_ge positive)))

public theorem Int32.toNatClampNeg_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int32.toNatClampNeg_ofNat_of_lt._proof_1_2) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 31))) (Int.natCast_nonneg _))

public theorem Int32.toNatClampNeg_ofNat_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int32.toNatClampNeg_ofNat_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem Int64.toInt_neg_ofNat_of_le._proof_1_1 :
    type_of% (private_decl% @_root_.Int64.toInt_neg_ofNat_of_le._proof_1_1) :=
  fun h impossible => impossible (Int.neg_le_neg (Int.ofNat_le.mpr h))

public theorem Int64.toInt_neg_ofNat_of_le._proof_1_2 :
    type_of% (private_decl% @_root_.Int64.toInt_neg_ofNat_of_le._proof_1_2) :=
  fun _ impossible => impossible (Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.pow_pos (by decide : (0 : Int) < 2)))

public theorem Int64.toInt_ofNat_of_lt._proof_1_1 :
    type_of% (private_decl% @_root_.Int64.toInt_ofNat_of_lt._proof_1_1) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 63))) (Int.natCast_nonneg _))

public theorem Int64.toInt_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int64.toInt_ofNat_of_lt._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem Int64.toNatClampNeg_ofIntClamp_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int64.toNatClampNeg_ofIntClamp_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.le_sub_one_of_lt h)

public theorem Int64.toNatClampNeg_ofIntClamp_of_lt._proof_1_4 :
    type_of% (private_decl% @_root_.Int64.toNatClampNeg_ofIntClamp_of_lt._proof_1_4) :=
  fun negative positive => negative (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 63))) (Int.le_of_lt (Int.lt_of_not_ge positive)))

public theorem Int64.toNatClampNeg_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.Int64.toNatClampNeg_ofNat_of_lt._proof_1_2) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 63))) (Int.natCast_nonneg _))

public theorem Int64.toNatClampNeg_ofNat_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.Int64.toNatClampNeg_ofNat_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.le_toInt._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.le_toInt._proof_1_1) :=
  fun _ lower impossible => impossible (Int.le_trans (Int.neg_le_neg (Int.ofNat_le.mpr (by decide : 2147483648 ≤ 9223372036854775808))) lower)

public theorem ISize.toInt64_ne_minValue._proof_1_3 :
    type_of% (private_decl% @_root_.ISize.toInt64_ne_minValue._proof_1_3) :=
  fun _ lower minimum distinct eq => distinct (Int.le_antisymm (eq ▸ minimum) lower)

public theorem ISize.toInt64_ofNat._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toInt64_ofNat._proof_1_1) :=
  fun h impossible => impossible (Int.ofNat_le.mpr h)

public theorem ISize.toInt64_ofNat._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toInt64_ofNat._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_le.mpr
    (Nat.le_trans h (by decide : 2147483647 ≤ 9223372036854775807)))

public theorem ISize.toInt_lt._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toInt_lt._proof_1_1) :=
  fun _ upper impossible => impossible (Int.lt_of_lt_of_le upper (Int.ofNat_le.mpr (by decide : 2147483648 ≤ 9223372036854775808)))

public theorem ISize.toInt_neg_ofNat_of_le._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toInt_neg_ofNat_of_le._proof_1_1) :=
  fun h impossible => impossible (Int.neg_le_neg (Int.ofNat_le.mpr h))

public theorem ISize.toInt_neg_ofNat_of_le._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toInt_neg_ofNat_of_le._proof_1_2) :=
  fun _ impossible => impossible (Int.lt_of_le_of_lt
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.pow_pos (by decide : (0 : Int) < 2)))

public theorem ISize.toInt_ofInt_of_le._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toInt_ofInt_of_le._proof_1_2) :=
  fun lower _ impossible => impossible (Int.le_trans (Int.neg_le_neg (Int.ofNat_le.mpr (by decide : 2147483648 ≤ 9223372036854775808))) lower)

public theorem ISize.toInt_ofInt_of_le._proof_1_3 :
    type_of% (private_decl% @_root_.ISize.toInt_ofInt_of_le._proof_1_3) :=
  fun _ upper impossible => impossible (Int.lt_of_lt_of_le upper (Int.ofNat_le.mpr (by decide : 2147483648 ≤ 9223372036854775808)))

public theorem ISize.toInt_ofNat_of_lt._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toInt_ofNat_of_lt._proof_1_1) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 31))) (Int.natCast_nonneg _))

public theorem ISize.toInt_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toInt_ofNat_of_lt._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.toInt_ofNat_of_lt_two_pow_numBits._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits._proof_1_1) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.toInt_ofNat_of_lt_two_pow_numBits._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.toNatClampNeg_neg_ofNat_of_le._proof_1_1 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_neg_ofNat_of_le._proof_1_1) :=
  fun h impossible => impossible (Int.neg_le_neg (Int.ofNat_le.mpr h))

public theorem ISize.toNatClampNeg_neg_ofNat_of_le._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_neg_ofNat_of_le._proof_1_2) :=
  fun _ impossible => impossible (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _))

public theorem ISize.toNatClampNeg_ofInt_eq_zero._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_ofInt_eq_zero._proof_1_2) :=
  fun _ nonpos impossible => impossible (Int.lt_of_le_of_lt nonpos (Int.pow_pos (by decide : (0 : Int) < 2)))

public theorem ISize.toNatClampNeg_ofNat_of_lt._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_ofNat_of_lt._proof_1_2) :=
  fun _ impossible => impossible (Int.le_trans
    (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg (2 ^ 31))) (Int.natCast_nonneg _))

public theorem ISize.toNatClampNeg_ofNat_of_lt._proof_1_3 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_ofNat_of_lt._proof_1_3) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits._proof_1_2 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits._proof_1_2) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

public theorem ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits._proof_1_3 :
    type_of% (private_decl% @_root_.ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits._proof_1_3) :=
  fun h impossible => impossible (Int.ofNat_lt.mpr h)

end OmegaChecks.InitPort.Alternatives
