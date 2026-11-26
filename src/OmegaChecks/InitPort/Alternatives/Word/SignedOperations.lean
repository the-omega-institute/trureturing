module

public import OmegaChecks.InitPort.Alternatives.Word.SignedConversions
import all OmegaChecks.InitPort.Alternatives.Word.Limits

namespace OmegaChecks.InitPort.Alternatives

public theorem Int32.toInt8_toInt16 : type_of% @_root_.Int32.toInt8_toInt16 := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int16.toInt_toInt8, _root_.Int32.toInt_toInt16, _root_.Int32.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 16))

public theorem Int64.toInt8_toInt16 : type_of% @_root_.Int64.toInt8_toInt16 := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int16.toInt_toInt8, _root_.Int64.toInt_toInt16, _root_.Int64.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 16))

public theorem Int64.toInt8_toInt32 : type_of% @_root_.Int64.toInt8_toInt32 := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int32.toInt_toInt8, _root_.Int64.toInt_toInt32, _root_.Int64.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 32))

public theorem Int64.toInt16_toInt32 : type_of% @_root_.Int64.toInt16_toInt32 := by
  intro n
  apply _root_.Int16.toInt.inj
  rw [_root_.Int32.toInt_toInt16, _root_.Int64.toInt_toInt32, _root_.Int64.toInt_toInt16]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))

public theorem ISize.toInt8_toInt16 : type_of% @_root_.ISize.toInt8_toInt16 := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int16.toInt_toInt8, _root_.ISize.toInt_toInt16, _root_.ISize.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 16))

public theorem ISize.toInt8_toInt32 : type_of% @_root_.ISize.toInt8_toInt32 := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.Int32.toInt_toInt8, _root_.ISize.toInt_toInt32, _root_.ISize.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 32))

public theorem ISize.toInt16_toInt32 : type_of% @_root_.ISize.toInt16_toInt32 := by
  intro n
  apply _root_.Int16.toInt.inj
  rw [_root_.Int32.toInt_toInt16, _root_.ISize.toInt_toInt32, _root_.ISize.toInt_toInt16]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by decide : 16 ≤ 32))

public theorem Int64.toInt8_toISize : type_of% @_root_.Int64.toInt8_toISize := by
  intro n
  apply _root_.Int8.toInt.inj
  rw [_root_.ISize.toInt_toInt8, _root_.Int64.toInt_toISize, _root_.Int64.toInt_toInt8]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 8 ≤ 32) System.Platform.le_numBits))

public theorem Int64.toInt16_toISize : type_of% @_root_.Int64.toInt16_toISize := by
  intro n
  apply _root_.Int16.toInt.inj
  rw [_root_.ISize.toInt_toInt16, _root_.Int64.toInt_toISize, _root_.Int64.toInt_toInt16]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (Nat.le_trans (by decide : 16 ≤ 32) System.Platform.le_numBits))

public theorem Int64.toInt32_toISize : type_of% @_root_.Int64.toInt32_toISize := by
  intro n
  apply _root_.Int32.toInt.inj
  rw [_root_.ISize.toInt_toInt32, _root_.Int64.toInt_toISize, _root_.Int64.toInt_toInt32]
  exact Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 System.Platform.le_numBits)

public theorem Int16.neg_eq_neg_one_mul : type_of% @_root_.Int16.neg_eq_neg_one_mul := by
  intro a
  apply _root_.Int16.toBitVec.inj
  rw [_root_.Int16.toBitVec_neg, _root_.Int16.toBitVec_mul, _root_.Int16.toBitVec_neg, _root_.Int16.toBitVec_one]
  exact _root_.BitVec.neg_eq_neg_one_mul _

public theorem Int32.neg_eq_neg_one_mul : type_of% @_root_.Int32.neg_eq_neg_one_mul := by
  intro a
  apply _root_.Int32.toBitVec.inj
  rw [_root_.Int32.toBitVec_neg, _root_.Int32.toBitVec_mul, _root_.Int32.toBitVec_neg, _root_.Int32.toBitVec_one]
  exact _root_.BitVec.neg_eq_neg_one_mul _

public theorem Int64.neg_eq_neg_one_mul : type_of% @_root_.Int64.neg_eq_neg_one_mul := by
  intro a
  apply _root_.Int64.toBitVec.inj
  rw [_root_.Int64.toBitVec_neg, _root_.Int64.toBitVec_mul, _root_.Int64.toBitVec_neg, _root_.Int64.toBitVec_one]
  exact _root_.BitVec.neg_eq_neg_one_mul _

public theorem Int64.toInt_neg_ofNat_of_le : type_of% @_root_.Int64.toInt_neg_ofNat_of_le := by
  intro n h
  rw [_root_.Int64.neg_ofNat]
  exact _root_.Int64.toInt_ofInt_of_le (Int.neg_le_neg (Int.ofNat_le.mpr h))
    (Int.lt_of_le_of_lt (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.pow_pos (by decide)))

public theorem ISize.toInt_neg_ofNat_of_le : type_of% @_root_.ISize.toInt_neg_ofNat_of_le := by
  intro n h
  rw [_root_.ISize.neg_ofNat]
  exact _root_.ISize.toInt_ofInt_of_le (Int.neg_le_neg (Int.ofNat_le.mpr h))
    (Int.lt_of_le_of_lt (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.pow_pos (by decide)))

public theorem ISize.toNatClampNeg_neg_ofNat_of_le : type_of% @_root_.ISize.toNatClampNeg_neg_ofNat_of_le := by
  intro n h
  exact (congrArg Int.toNat (ISize.toInt_neg_ofNat_of_le h)).trans
    (Int.toNat_eq_zero.mpr (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)))

public theorem ISize.toNatClampNeg_ofInt_eq_zero : type_of% @_root_.ISize.toNatClampNeg_ofInt_eq_zero := by
  intro n lo hi
  exact (congrArg Int.toNat (_root_.ISize.toInt_ofInt_of_le lo
    (Int.lt_of_le_of_lt hi (Int.pow_pos (by decide))))).trans (Int.toNat_eq_zero.mpr hi)

public theorem ISize.toNatClampNeg_ofIntClamp_of_lt : type_of% @_root_.ISize.toNatClampNeg_ofIntClamp_of_lt := by
  intro n hi
  apply _root_.ISize.toNatClampNeg_ofIntClamp_of_lt_two_pow_numBits
  exact Int.lt_of_lt_of_le hi (Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two
    (Nat.sub_le_sub_right System.Platform.le_numBits 1)))

public theorem Int8.div_self : type_of% @_root_.Int8.div_self := by
  intro a
  if zero : a = 0 then
    rw [ite_eq_left zero, zero, _root_.Int8.div_zero]
  else
    rw [ite_eq_right zero]
    apply _root_.Int8.toInt.inj
    have nz : a.toInt ≠ 0 := fun h => zero (_root_.Int8.toInt.inj (h.trans _root_.Int8.toInt_zero.symm))
    rw [_root_.Int8.toInt_div, Int.tdiv_self nz, ← _root_.Int8.toInt_ofInt]
    exact rfl

public theorem Int16.div_self : type_of% @_root_.Int16.div_self := by
  intro a
  if zero : a = 0 then
    rw [ite_eq_left zero, zero, _root_.Int16.div_zero]
  else
    rw [ite_eq_right zero]
    apply _root_.Int16.toInt.inj
    have nz : a.toInt ≠ 0 := fun h => zero (_root_.Int16.toInt.inj (h.trans _root_.Int16.toInt_zero.symm))
    rw [_root_.Int16.toInt_div, Int.tdiv_self nz, ← _root_.Int16.toInt_ofInt]
    exact rfl

public theorem Int32.div_self : type_of% @_root_.Int32.div_self := by
  intro a
  if zero : a = 0 then
    rw [ite_eq_left zero, zero, _root_.Int32.div_zero]
  else
    rw [ite_eq_right zero]
    apply _root_.Int32.toInt.inj
    have nz : a.toInt ≠ 0 := fun h => zero (_root_.Int32.toInt.inj (h.trans _root_.Int32.toInt_zero.symm))
    rw [_root_.Int32.toInt_div, Int.tdiv_self nz, ← _root_.Int32.toInt_ofInt]
    exact rfl

public theorem Int64.div_self : type_of% @_root_.Int64.div_self := by
  intro a
  if zero : a = 0 then
    rw [ite_eq_left zero, zero, _root_.Int64.div_zero]
  else
    rw [ite_eq_right zero]
    apply _root_.Int64.toInt.inj
    have nz : a.toInt ≠ 0 := fun h => zero (_root_.Int64.toInt.inj (h.trans _root_.Int64.toInt_zero.symm))
    rw [_root_.Int64.toInt_div, Int.tdiv_self nz, ← _root_.Int64.toInt_ofInt]
    exact rfl

public theorem ISize.div_self : type_of% @_root_.ISize.div_self := by
  intro a
  if zero : a = 0 then
    rw [ite_eq_left zero, zero, _root_.ISize.div_zero]
  else
    rw [ite_eq_right zero]
    apply _root_.ISize.toInt.inj
    have nz : a.toInt ≠ 0 := fun h => zero (_root_.ISize.toInt.inj (h.trans _root_.ISize.toInt_zero.symm))
    rw [_root_.ISize.toInt_div, Int.tdiv_self nz, ← _root_.ISize.toInt_ofInt]
    exact rfl

public theorem Int16.toInt32_neg_of_ne : type_of% @_root_.Int16.toInt32_neg_of_ne := by
  intro x hx
  apply _root_.Int32.toBitVec.inj
  rw [_root_.Int16.toBitVec_toInt32, _root_.Int16.toBitVec_neg, _root_.Int32.toBitVec_neg,
    _root_.Int16.toBitVec_toInt32]
  apply _root_.BitVec.signExtend_neg_of_ne_intMin
  exact fun eq => hx (_root_.Int16.toBitVec.inj (eq.trans _root_.Int16.toBitVec_minValue.symm))

public theorem Int16.toInt64_neg_of_ne : type_of% @_root_.Int16.toInt64_neg_of_ne := by
  intro x hx
  apply _root_.Int64.toBitVec.inj
  rw [_root_.Int16.toBitVec_toInt64, _root_.Int16.toBitVec_neg, _root_.Int64.toBitVec_neg,
    _root_.Int16.toBitVec_toInt64]
  apply _root_.BitVec.signExtend_neg_of_ne_intMin
  exact fun eq => hx (_root_.Int16.toBitVec.inj (eq.trans _root_.Int16.toBitVec_minValue.symm))

public theorem Int16.toISize_neg_of_ne : type_of% @_root_.Int16.toISize_neg_of_ne := by
  intro x hx
  apply _root_.ISize.toBitVec.inj
  rw [_root_.Int16.toBitVec_toISize, _root_.Int16.toBitVec_neg, _root_.ISize.toBitVec_neg,
    _root_.Int16.toBitVec_toISize]
  apply _root_.BitVec.signExtend_neg_of_ne_intMin
  exact fun eq => hx (_root_.Int16.toBitVec.inj (eq.trans _root_.Int16.toBitVec_minValue.symm))

public theorem Int32.toInt64_neg_of_ne : type_of% @_root_.Int32.toInt64_neg_of_ne := by
  intro x hx
  apply _root_.Int64.toBitVec.inj
  rw [_root_.Int32.toBitVec_toInt64, _root_.Int32.toBitVec_neg, _root_.Int64.toBitVec_neg,
    _root_.Int32.toBitVec_toInt64]
  apply _root_.BitVec.signExtend_neg_of_ne_intMin
  exact fun eq => hx (_root_.Int32.toBitVec.inj (eq.trans _root_.Int32.toBitVec_minValue.symm))

public theorem Int32.toISize_neg_of_ne : type_of% @_root_.Int32.toISize_neg_of_ne := by
  intro x hx
  apply _root_.ISize.toBitVec.inj
  rw [_root_.Int32.toBitVec_toISize, _root_.Int32.toBitVec_neg, _root_.ISize.toBitVec_neg,
    _root_.Int32.toBitVec_toISize]
  apply _root_.BitVec.signExtend_neg_of_ne_intMin
  exact fun eq => hx (_root_.Int32.toBitVec.inj (eq.trans _root_.Int32.toBitVec_minValue.symm))

public theorem BitVec.neg_sle_zero : type_of% @_root_.BitVec.neg_sle_zero := by
  intro w hw x
  apply Bool.eq_iff_iff.mpr
  apply _root_.BitVec.sle_iff_toInt_le.trans
  apply Iff.trans ?_ Bool.or_eq_true_iff.symm
  if eq : x = _root_.BitVec.intMin w then
    refine ⟨fun _ => Or.inl (beq_iff_eq.mpr eq), fun _ => ?_⟩
    rw [eq, _root_.BitVec.neg_intMin, _root_.BitVec.toInt_intMin_of_pos hw, _root_.BitVec.toInt_zero]
    exact Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))
  else
    rw [_root_.BitVec.toInt_neg_of_ne_intMin eq, _root_.BitVec.toInt_zero]
    have positive : (0#w).sle x = true ↔ 0 ≤ x.toInt := by
      apply _root_.BitVec.sle_iff_toInt_le.trans
      rw [_root_.BitVec.toInt_zero]
    exact ⟨fun h => Or.inr (positive.mpr (Int.nonneg_of_neg_nonpos h)), fun h =>
      Int.neg_nonpos_of_nonneg (positive.mp (h.resolve_left (fun beq => eq (eq_of_beq beq))))⟩

public theorem Int8.neg_nonpos_iff : type_of% @_root_.Int8.neg_nonpos_iff := by
  intro n
  apply _root_.Int8.le_iff_toBitVec_sle.trans
  rw [_root_.Int8.toBitVec_neg, _root_.Int8.toBitVec_zero, BitVec.neg_sle_zero (Nat.zero_lt_succ _)]
  apply Bool.or_eq_true_iff.trans
  apply or_congr
  · apply beq_iff_eq.trans
    rw [← _root_.Int8.toBitVec_minValue]
    exact _root_.Int8.toBitVec_inj
  · apply Iff.trans ?_ _root_.Int8.le_iff_toBitVec_sle.symm
    rw [_root_.Int8.toBitVec_zero]

public theorem Int16.neg_nonpos_iff : type_of% @_root_.Int16.neg_nonpos_iff := by
  intro n
  apply _root_.Int16.le_iff_toBitVec_sle.trans
  rw [_root_.Int16.toBitVec_neg, _root_.Int16.toBitVec_zero, BitVec.neg_sle_zero (Nat.zero_lt_succ _)]
  apply Bool.or_eq_true_iff.trans
  apply or_congr
  · apply beq_iff_eq.trans
    rw [← _root_.Int16.toBitVec_minValue]
    exact _root_.Int16.toBitVec_inj
  · apply Iff.trans ?_ _root_.Int16.le_iff_toBitVec_sle.symm
    rw [_root_.Int16.toBitVec_zero]

public theorem Int32.neg_nonpos_iff : type_of% @_root_.Int32.neg_nonpos_iff := by
  intro n
  apply _root_.Int32.le_iff_toBitVec_sle.trans
  rw [_root_.Int32.toBitVec_neg, _root_.Int32.toBitVec_zero, BitVec.neg_sle_zero (Nat.zero_lt_succ _)]
  apply Bool.or_eq_true_iff.trans
  apply or_congr
  · apply beq_iff_eq.trans
    rw [← _root_.Int32.toBitVec_minValue]
    exact _root_.Int32.toBitVec_inj
  · apply Iff.trans ?_ _root_.Int32.le_iff_toBitVec_sle.symm
    rw [_root_.Int32.toBitVec_zero]

public theorem Int64.neg_nonpos_iff : type_of% @_root_.Int64.neg_nonpos_iff := by
  intro n
  apply _root_.Int64.le_iff_toBitVec_sle.trans
  rw [_root_.Int64.toBitVec_neg, _root_.Int64.toBitVec_zero, BitVec.neg_sle_zero (Nat.zero_lt_succ _)]
  apply Bool.or_eq_true_iff.trans
  apply or_congr
  · apply beq_iff_eq.trans
    rw [← _root_.Int64.toBitVec_minValue]
    exact _root_.Int64.toBitVec_inj
  · apply Iff.trans ?_ _root_.Int64.le_iff_toBitVec_sle.symm
    rw [_root_.Int64.toBitVec_zero]

public theorem ISize.neg_nonpos_iff : type_of% @_root_.ISize.neg_nonpos_iff := by
  intro n
  apply _root_.ISize.le_iff_toBitVec_sle.trans
  rw [_root_.ISize.toBitVec_neg, _root_.ISize.toBitVec_zero, BitVec.neg_sle_zero System.Platform.numBits_pos]
  apply Bool.or_eq_true_iff.trans
  apply or_congr
  · apply beq_iff_eq.trans
    rw [← _root_.ISize.toBitVec_minValue]
    exact _root_.ISize.toBitVec_inj
  · apply Iff.trans ?_ _root_.ISize.le_iff_toBitVec_sle.symm
    rw [_root_.ISize.toBitVec_zero]

public theorem Int8.toISize_ne_minValue : type_of% @_root_.Int8.toISize_ne_minValue := by
  intro n e
  have equal := congrArg _root_.ISize.toInt e
  rw [_root_.Int8.toInt_toISize] at equal
  have small : (2 : Int) ^ 7 < 2 ^ 31 := Int.ofNat_lt.mpr
    (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 7 < 31))
  exact Int.not_lt_of_ge (_root_.Int8.le_toInt n)
    (equal ▸ Int.lt_of_le_of_lt _root_.ISize.toInt_minValue_le (Int.neg_lt_neg small))

public theorem Int16.toISize_ne_minValue : type_of% @_root_.Int16.toISize_ne_minValue := by
  intro n e
  have equal := congrArg _root_.ISize.toInt e
  rw [_root_.Int16.toInt_toISize] at equal
  have small : (2 : Int) ^ 15 < 2 ^ 31 := Int.ofNat_lt.mpr
    (Nat.pow_lt_pow_right Nat.one_lt_two (by decide : 15 < 31))
  exact Int.not_lt_of_ge (_root_.Int16.le_toInt n)
    (equal ▸ Int.lt_of_le_of_lt _root_.ISize.toInt_minValue_le (Int.neg_lt_neg small))

public theorem Int32.toISize_ne_minValue : type_of% @_root_.Int32.toISize_ne_minValue := by
  intro n hn e
  apply hn
  apply _root_.Int32.toInt.inj
  apply Int.le_antisymm _ n.minValue_le_toInt
  have equal := congrArg _root_.ISize.toInt e
  rw [_root_.Int32.toInt_toISize] at equal
  rw [equal, _root_.Int32.toInt_minValue]
  exact _root_.ISize.toInt_minValue_le

public theorem ISize.toInt64_ne_minValue : type_of% @_root_.ISize.toInt64_ne_minValue := by
  intro n hn e
  apply hn
  apply _root_.ISize.toInt.inj
  apply Int.le_antisymm _ n.minValue_le_toInt
  have equal := congrArg _root_.Int64.toInt e
  rw [_root_.ISize.toInt_toInt64] at equal
  rw [equal]
  exact _root_.ISize.minValue.int64MinValue_le_toInt

public theorem Int16.toInt32_ofNat : type_of% @_root_.Int16.toInt32_ofNat := by
  intro n h
  apply _root_.Int16.toInt32_ofNat'
  rw [_root_.Int16.toInt_maxValue]
  have lt : n < 2^15 := by
    rw [← ones_add_one 15]
    exact Nat.lt_succ_of_le h
  exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt)

public theorem Int16.toInt64_ofNat : type_of% @_root_.Int16.toInt64_ofNat := by
  intro n h
  apply _root_.Int16.toInt64_ofNat'
  rw [_root_.Int16.toInt_maxValue]
  have lt : n < 2^15 := by
    rw [← ones_add_one 15]
    exact Nat.lt_succ_of_le h
  exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt)

public theorem Int32.toInt64_ofNat : type_of% @_root_.Int32.toInt64_ofNat := by
  intro n h
  apply _root_.Int32.toInt64_ofNat'
  rw [_root_.Int32.toInt_maxValue]
  have lt : n < 2^31 := by
    rw [← ones_add_one 31]
    exact Nat.lt_succ_of_le h
  exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt)

public theorem Int16.toISize_ofNat : type_of% @_root_.Int16.toISize_ofNat := by
  intro n h
  apply _root_.Int16.toISize_ofNat'
  rw [_root_.Int16.toInt_maxValue]
  have lt : n < 2^15 := by
    rw [← ones_add_one 15]
    exact Nat.lt_succ_of_le h
  exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt)

public theorem Int32.toISize_ofNat : type_of% @_root_.Int32.toISize_ofNat := by
  intro n h
  apply _root_.Int32.toISize_ofNat'
  rw [_root_.Int32.toInt_maxValue]
  have lt : n < 2^31 := by
    rw [← ones_add_one 31]
    exact Nat.lt_succ_of_le h
  exact Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt)

public theorem ISize.toInt64_ofNat : type_of% @_root_.ISize.toInt64_ofNat := by
  intro n h
  apply _root_.ISize.toInt64_ofNat'
  have lt : n < 2^31 := by
    rw [← ones_add_one 31]
    exact Nat.lt_succ_of_le h
  exact Int.le_trans (Int.le_sub_one_of_lt (Int.ofNat_lt.mpr lt))
    _root_.ISize.le_toInt_maxValue

end OmegaChecks.InitPort.Alternatives
