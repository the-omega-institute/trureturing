module

public import OmegaChecks.InitPort.Alternatives.Word.Limits

namespace OmegaChecks.InitPort.Alternatives

private theorem int8_bmod_of_large (x : _root_.Int8) (m : Nat) (wide : (256 : Int) ≤ m) :
    x.toInt.bmod m = x.toInt := by
  apply Int.bmod_eq_of_le_mul_two
  · rw [Int.mul_comm]
    exact Int.le_trans (Int.neg_le_neg wide) (BitVec.le_two_mul_toInt (x := x.toBitVec))
  · rw [Int.mul_comm]
    exact Int.lt_of_lt_of_le (BitVec.two_mul_toInt_lt (x := x.toBitVec)) wide

public theorem Int8.toInt_bmod_65536 : type_of% @_root_.Int8.toInt_bmod_65536 :=
  fun x => int8_bmod_of_large x 65536 (by decide)

public theorem Int8.toInt_bmod_4294967296 : type_of% @_root_.Int8.toInt_bmod_4294967296 :=
  fun x => int8_bmod_of_large x 4294967296 (by decide)

public theorem Int8.toInt_bmod_18446744073709551616 : type_of% @_root_.Int8.toInt_bmod_18446744073709551616 :=
  fun x => int8_bmod_of_large x 18446744073709551616 (by decide)

public theorem Int16.toInt_lt : type_of% @_root_.Int16.toInt_lt := by
  intro x
  rw [← _root_.Int16.toInt_toBitVec]
  exact _root_.BitVec.toInt_lt

public theorem Int16.le_toInt : type_of% @_root_.Int16.le_toInt := by
  intro x
  rw [← _root_.Int16.toInt_toBitVec]
  exact _root_.BitVec.le_toInt x.toBitVec

public theorem Int16.toInt_le : type_of% @_root_.Int16.toInt_le := by
  intro x
  rw [_root_.Int16.toInt_maxValue]
  exact Int.le_sub_one_of_lt (Int16.toInt_lt x)

public theorem Int16.minValue_le_toInt : type_of% @_root_.Int16.minValue_le_toInt := by
  intro x
  rw [_root_.Int16.toInt_minValue]
  exact Int16.le_toInt x

public theorem Int32.toInt_lt : type_of% @_root_.Int32.toInt_lt := by
  intro x
  rw [← _root_.Int32.toInt_toBitVec]
  exact _root_.BitVec.toInt_lt

public theorem Int32.le_toInt : type_of% @_root_.Int32.le_toInt := by
  intro x
  rw [← _root_.Int32.toInt_toBitVec]
  exact _root_.BitVec.le_toInt x.toBitVec

public theorem Int32.toInt_le : type_of% @_root_.Int32.toInt_le := by
  intro x
  rw [_root_.Int32.toInt_maxValue]
  exact Int.le_sub_one_of_lt (Int32.toInt_lt x)

public theorem Int32.minValue_le_toInt : type_of% @_root_.Int32.minValue_le_toInt := by
  intro x
  rw [_root_.Int32.toInt_minValue]
  exact Int32.le_toInt x

public theorem Int64.toInt_lt : type_of% @_root_.Int64.toInt_lt := by
  intro x
  rw [← _root_.Int64.toInt_toBitVec]
  exact _root_.BitVec.toInt_lt

public theorem Int64.le_toInt : type_of% @_root_.Int64.le_toInt := by
  intro x
  rw [← _root_.Int64.toInt_toBitVec]
  exact _root_.BitVec.le_toInt x.toBitVec

public theorem Int64.toInt_le : type_of% @_root_.Int64.toInt_le := by
  intro x
  rw [_root_.Int64.toInt_maxValue]
  exact Int.le_sub_one_of_lt (Int64.toInt_lt x)

public theorem Int64.minValue_le_toInt : type_of% @_root_.Int64.minValue_le_toInt := by
  intro x
  rw [_root_.Int64.toInt_minValue]
  exact Int64.le_toInt x

public theorem ISize.toInt_maxValue : type_of% @_root_.ISize.toInt_maxValue := by
  apply _root_.ISize.toInt_ofInt_of_two_pow_numBits_le
  · have pos : 0 < (2 : Int) ^ (System.Platform.numBits-1) := Int.pow_pos (by decide)
    omega
  · omega

public theorem ISize.toInt_le : type_of% @_root_.ISize.toInt_le := by
  intro x
  rw [ISize.toInt_maxValue]
  exact Int.le_sub_one_of_lt (_root_.ISize.toInt_lt_two_pow_numBits x)

public theorem ISize.toInt_lt : type_of% @_root_.ISize.toInt_lt := by
  intro x
  have exp := Nat.sub_le_sub_right System.Platform.numBits_le 1
  have bound := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two exp
  exact Int.lt_of_lt_of_le (_root_.ISize.toInt_lt_two_pow_numBits x) (Int.ofNat_le.mpr bound)

public theorem ISize.le_toInt : type_of% @_root_.ISize.le_toInt := by
  intro x
  have exp := Nat.sub_le_sub_right System.Platform.numBits_le 1
  have bound := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two exp
  exact Int.le_trans (Int.neg_le_neg (Int.ofNat_le.mpr bound)) (_root_.ISize.two_pow_numBits_le_toInt x)

public theorem ISize.toInt_minValue_le : type_of% @_root_.ISize.toInt_minValue_le := by
  rw [_root_.ISize.toInt_minValue]
  exact Int.neg_le_neg (Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two
    (Nat.sub_le_sub_right System.Platform.le_numBits 1)))

public theorem ISize.le_toInt_maxValue : type_of% @_root_.ISize.le_toInt_maxValue := by
  rw [ISize.toInt_maxValue]
  exact Int.sub_le_sub_right (Int.ofNat_le.mpr (Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two
    (Nat.sub_le_sub_right System.Platform.le_numBits 1))) _

public theorem Int16.toInt_ofIntLE : type_of% @_root_.Int16.toInt_ofIntLE := by
  intro x lo hi
  rw [← _root_.Int16.toInt_toBitVec, _root_.Int16.toBitVec_ofIntLE]
  rw [_root_.Int16.toInt_minValue] at lo
  rw [_root_.Int16.toInt_maxValue] at hi
  exact _root_.BitVec.toInt_ofInt_eq_self (Nat.zero_lt_succ 15) lo (Int.lt_of_le_sub_one hi)

public theorem Int32.toInt_ofIntLE : type_of% @_root_.Int32.toInt_ofIntLE := by
  intro x lo hi
  rw [← _root_.Int32.toInt_toBitVec, _root_.Int32.toBitVec_ofIntLE]
  rw [_root_.Int32.toInt_minValue] at lo
  rw [_root_.Int32.toInt_maxValue] at hi
  exact _root_.BitVec.toInt_ofInt_eq_self (Nat.zero_lt_succ 31) lo (Int.lt_of_le_sub_one hi)

public theorem Int64.toInt_ofIntLE : type_of% @_root_.Int64.toInt_ofIntLE := by
  intro x lo hi
  rw [← _root_.Int64.toInt_toBitVec, _root_.Int64.toBitVec_ofIntLE]
  rw [_root_.Int64.toInt_minValue] at lo
  rw [_root_.Int64.toInt_maxValue] at hi
  exact _root_.BitVec.toInt_ofInt_eq_self (Nat.zero_lt_succ 63) lo (Int.lt_of_le_sub_one hi)

public theorem Int16.iSizeMinValue_le_toInt : type_of% @_root_.Int16.iSizeMinValue_le_toInt := by
  intro x
  have bound : (2 : Int) ^ 15 ≤ 2 ^ 31 := Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 31))
  exact Int.le_trans ISize.toInt_minValue_le (Int.le_trans (Int.neg_le_neg bound) (Int16.le_toInt x))

public theorem Int16.toInt_le_iSizeMaxValue : type_of% @_root_.Int16.toInt_le_iSizeMaxValue := by
  intro x
  have bound : (2 : Int) ^ 15 ≤ 2 ^ 31 := Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 15 ≤ 31))
  exact Int.le_trans (Int.le_sub_one_of_lt (Int16.toInt_lt x)) (Int.le_trans (Int.sub_le_sub_right bound 1) ISize.le_toInt_maxValue)

public theorem Int32.iSizeMinValue_le_toInt : type_of% @_root_.Int32.iSizeMinValue_le_toInt := by
  intro x
  have bound : (2 : Int) ^ 31 ≤ 2 ^ 31 := Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 31 ≤ 31))
  exact Int.le_trans ISize.toInt_minValue_le (Int.le_trans (Int.neg_le_neg bound) (Int32.le_toInt x))

public theorem Int32.toInt_le_iSizeMaxValue : type_of% @_root_.Int32.toInt_le_iSizeMaxValue := by
  intro x
  have bound : (2 : Int) ^ 31 ≤ 2 ^ 31 := Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (by decide : 31 ≤ 31))
  exact Int.le_trans (Int.le_sub_one_of_lt (Int32.toInt_lt x)) (Int.le_trans (Int.sub_le_sub_right bound 1) ISize.le_toInt_maxValue)

public theorem ISize.int64MinValue_le_toInt : type_of% @_root_.ISize.int64MinValue_le_toInt := by
  intro x
  rw [_root_.Int64.toInt_minValue]
  exact ISize.le_toInt x

public theorem ISize.toInt_le_int64MaxValue : type_of% @_root_.ISize.toInt_le_int64MaxValue := by
  intro x
  rw [_root_.Int64.toInt_maxValue]
  exact Int.le_sub_one_of_lt (ISize.toInt_lt x)

public theorem Int16.toInt_bmod : type_of% @_root_.Int16.toInt_bmod := by
  intro x
  rw [← _root_.Int16.toInt_toBitVec x]
  exact (_root_.BitVec.toInt_ofInt _ (n := 16)).symm.trans (congrArg _root_.BitVec.toInt _root_.BitVec.ofInt_toInt)

public theorem Int32.toInt_bmod : type_of% @_root_.Int32.toInt_bmod := by
  intro x
  rw [← _root_.Int32.toInt_toBitVec x]
  exact (_root_.BitVec.toInt_ofInt _ (n := 32)).symm.trans (congrArg _root_.BitVec.toInt _root_.BitVec.ofInt_toInt)

public theorem Int64.toInt_bmod : type_of% @_root_.Int64.toInt_bmod := by
  intro x
  rw [← _root_.Int64.toInt_toBitVec x]
  exact (_root_.BitVec.toInt_ofInt _ (n := 64)).symm.trans (congrArg _root_.BitVec.toInt _root_.BitVec.ofInt_toInt)

public theorem Int16.toInt_bmod_4294967296 : type_of% @_root_.Int16.toInt_bmod_4294967296 := by
  intro x
  rw [← _root_.Int16.toInt_toInt32 x]
  exact Int32.toInt_bmod _

public theorem Int16.toInt_bmod_18446744073709551616 : type_of% @_root_.Int16.toInt_bmod_18446744073709551616 := by
  intro x
  rw [← _root_.Int16.toInt_toInt64 x]
  exact Int64.toInt_bmod _

public theorem Int32.toInt_bmod_18446744073709551616 : type_of% @_root_.Int32.toInt_bmod_18446744073709551616 := by
  intro x
  rw [← _root_.Int32.toInt_toInt64 x]
  exact Int64.toInt_bmod _

public theorem ISize.toInt_bmod_18446744073709551616 : type_of% @_root_.ISize.toInt_bmod_18446744073709551616 := by
  intro x
  rw [← _root_.ISize.toInt_toInt64 x]
  exact Int64.toInt_bmod _

public theorem Int8.toInt_ofNat_of_lt : type_of% @_root_.Int8.toInt_ofNat_of_lt := by
  intro n h
  rw [← _root_.Int8.ofInt_eq_ofNat]
  exact _root_.Int8.toInt_ofInt_of_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem Int16.toInt_ofNat_of_lt : type_of% @_root_.Int16.toInt_ofNat_of_lt := by
  intro n h
  rw [← _root_.Int16.ofInt_eq_ofNat]
  exact _root_.Int16.toInt_ofInt_of_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem Int32.toInt_ofNat_of_lt : type_of% @_root_.Int32.toInt_ofNat_of_lt := by
  intro n h
  rw [← _root_.Int32.ofInt_eq_ofNat]
  exact _root_.Int32.toInt_ofInt_of_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem Int64.toInt_ofNat_of_lt : type_of% @_root_.Int64.toInt_ofNat_of_lt := by
  intro n h
  rw [← _root_.Int64.ofInt_eq_ofNat]
  exact _root_.Int64.toInt_ofInt_of_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem ISize.toInt_ofInt_of_le : type_of% @_root_.ISize.toInt_ofInt_of_le := by
  intro n lo hi
  have bound : (2 : Int) ^ 31 ≤ 2 ^ (System.Platform.numBits - 1) :=
    Int.ofNat_le.mpr (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.sub_le_sub_right System.Platform.le_numBits 1))
  exact _root_.ISize.toInt_ofInt_of_two_pow_numBits_le (Int.le_trans (Int.neg_le_neg bound) lo)
    (Int.lt_of_lt_of_le hi bound)

public theorem ISize.toInt_ofNat_of_lt : type_of% @_root_.ISize.toInt_ofNat_of_lt := by
  intro n h
  rw [← _root_.ISize.ofInt_eq_ofNat]
  exact ISize.toInt_ofInt_of_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem Int16.toNatClampNeg_ofIntLE : type_of% @_root_.Int16.toNatClampNeg_ofIntLE :=
  fun h₁ h₂ => congrArg Int.toNat (Int16.toInt_ofIntLE (h₁ := h₁) (h₂ := h₂))

public theorem Int32.toNatClampNeg_ofIntLE : type_of% @_root_.Int32.toNatClampNeg_ofIntLE :=
  fun h₁ h₂ => congrArg Int.toNat (Int32.toInt_ofIntLE (h₁ := h₁) (h₂ := h₂))

public theorem Int64.toNatClampNeg_ofIntLE : type_of% @_root_.Int64.toNatClampNeg_ofIntLE :=
  fun h₁ h₂ => congrArg Int.toNat (Int64.toInt_ofIntLE (h₁ := h₁) (h₂ := h₂))

public theorem ISize.toInt_ofNat_of_lt_two_pow_numBits : type_of% @_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits := by
  intro n h
  rw [← _root_.ISize.ofInt_eq_ofNat]
  exact _root_.ISize.toInt_ofInt_of_two_pow_numBits_le
    (Int.le_trans (Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide))) (Int.natCast_nonneg n)) (Int.ofNat_lt.mpr h)

public theorem Int8.toInt_div_of_ne_left : type_of% @_root_.Int8.toInt_div_of_ne_left := by
  intro a b h
  have ne : a.toBitVec ≠ _root_.BitVec.intMin 8 := fun eq =>
    h (_root_.Int8.toBitVec_inj.mp (eq.trans _root_.Int8.toBitVec_minValue.symm))
  rw [← _root_.Int8.toInt_toBitVec, _root_.Int8.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inl ne), _root_.Int8.toInt_toBitVec, _root_.Int8.toInt_toBitVec]

public theorem Int8.toInt_div_of_ne_right : type_of% @_root_.Int8.toInt_div_of_ne_right := by
  intro a b h
  have neg : (-1 : Int8).toBitVec = -1#8 := (_root_.Int8.toBitVec_neg 1).trans
    (congrArg Neg.neg _root_.Int8.toBitVec_one)
  have ne := fun eq => h (_root_.Int8.toBitVec_inj.mp (Eq.trans eq neg.symm))
  rw [← _root_.Int8.toInt_toBitVec, _root_.Int8.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr ne), _root_.Int8.toInt_toBitVec, _root_.Int8.toInt_toBitVec]

public theorem Int16.toInt_div_of_ne_left : type_of% @_root_.Int16.toInt_div_of_ne_left := by
  intro a b h
  have ne : a.toBitVec ≠ _root_.BitVec.intMin 16 := fun eq =>
    h (_root_.Int16.toBitVec_inj.mp (eq.trans _root_.Int16.toBitVec_minValue.symm))
  rw [← _root_.Int16.toInt_toBitVec, _root_.Int16.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inl ne), _root_.Int16.toInt_toBitVec, _root_.Int16.toInt_toBitVec]

public theorem Int16.toInt_div_of_ne_right : type_of% @_root_.Int16.toInt_div_of_ne_right := by
  intro a b h
  have neg : (-1 : Int16).toBitVec = -1#16 := (_root_.Int16.toBitVec_neg 1).trans
    (congrArg Neg.neg _root_.Int16.toBitVec_one)
  have ne := fun eq => h (_root_.Int16.toBitVec_inj.mp (Eq.trans eq neg.symm))
  rw [← _root_.Int16.toInt_toBitVec, _root_.Int16.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr ne), _root_.Int16.toInt_toBitVec, _root_.Int16.toInt_toBitVec]

public theorem Int16.minValue_div_neg_one : type_of% @_root_.Int16.minValue_div_neg_one := by
  apply _root_.Int16.toBitVec_inj.mp
  rw [_root_.Int16.toBitVec_div, _root_.Int16.toBitVec_minValue, _root_.Int16.toBitVec_neg, _root_.Int16.toBitVec_one,
    _root_.BitVec.intMin_sdiv_neg_one]

public theorem Int32.toInt_div_of_ne_left : type_of% @_root_.Int32.toInt_div_of_ne_left := by
  intro a b h
  have ne : a.toBitVec ≠ _root_.BitVec.intMin 32 := fun eq =>
    h (_root_.Int32.toBitVec_inj.mp (eq.trans _root_.Int32.toBitVec_minValue.symm))
  rw [← _root_.Int32.toInt_toBitVec, _root_.Int32.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inl ne), _root_.Int32.toInt_toBitVec, _root_.Int32.toInt_toBitVec]

public theorem Int32.toInt_div_of_ne_right : type_of% @_root_.Int32.toInt_div_of_ne_right := by
  intro a b h
  have neg : (-1 : Int32).toBitVec = -1#32 := (_root_.Int32.toBitVec_neg 1).trans
    (congrArg Neg.neg _root_.Int32.toBitVec_one)
  have ne := fun eq => h (_root_.Int32.toBitVec_inj.mp (Eq.trans eq neg.symm))
  rw [← _root_.Int32.toInt_toBitVec, _root_.Int32.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr ne), _root_.Int32.toInt_toBitVec, _root_.Int32.toInt_toBitVec]

public theorem Int32.minValue_div_neg_one : type_of% @_root_.Int32.minValue_div_neg_one := by
  apply _root_.Int32.toBitVec_inj.mp
  rw [_root_.Int32.toBitVec_div, _root_.Int32.toBitVec_minValue, _root_.Int32.toBitVec_neg, _root_.Int32.toBitVec_one,
    _root_.BitVec.intMin_sdiv_neg_one]

public theorem Int64.toInt_div_of_ne_left : type_of% @_root_.Int64.toInt_div_of_ne_left := by
  intro a b h
  have ne : a.toBitVec ≠ _root_.BitVec.intMin 64 := fun eq =>
    h (_root_.Int64.toBitVec_inj.mp (eq.trans _root_.Int64.toBitVec_minValue.symm))
  rw [← _root_.Int64.toInt_toBitVec, _root_.Int64.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inl ne), _root_.Int64.toInt_toBitVec, _root_.Int64.toInt_toBitVec]

public theorem Int64.toInt_div_of_ne_right : type_of% @_root_.Int64.toInt_div_of_ne_right := by
  intro a b h
  have neg : (-1 : Int64).toBitVec = -1#64 := (_root_.Int64.toBitVec_neg 1).trans
    (congrArg Neg.neg _root_.Int64.toBitVec_one)
  have ne := fun eq => h (_root_.Int64.toBitVec_inj.mp (Eq.trans eq neg.symm))
  rw [← _root_.Int64.toInt_toBitVec, _root_.Int64.toBitVec_div,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr ne), _root_.Int64.toInt_toBitVec, _root_.Int64.toInt_toBitVec]

public theorem Int64.minValue_div_neg_one : type_of% @_root_.Int64.minValue_div_neg_one := by
  apply _root_.Int64.toBitVec_inj.mp
  rw [_root_.Int64.toBitVec_div, _root_.Int64.toBitVec_minValue, _root_.Int64.toBitVec_neg, _root_.Int64.toBitVec_one,
    _root_.BitVec.intMin_sdiv_neg_one]

public theorem BitVec.ofInt_iSizeToInt : type_of% @_root_.BitVec.ofInt_iSizeToInt := by
  intro x
  rw [← _root_.ISize.toInt_toBitVec]
  exact _root_.BitVec.ofInt_toInt

public theorem ISize.toNatClampNeg_lt_two_pow_numBits : type_of% @_root_.ISize.toNatClampNeg_lt_two_pow_numBits := by
  intro x
  exact (Int.toNat_lt' (Nat.two_pow_pos _)).mpr (_root_.ISize.toInt_lt_two_pow_numBits x)

public theorem ISize.toInt_bmod_two_pow_numBits : type_of% @_root_.ISize.toInt_bmod_two_pow_numBits := by
  intro x
  exact (_root_.BitVec.toInt_ofInt _).symm.trans ((congrArg _root_.BitVec.toInt (BitVec.ofInt_iSizeToInt x)).trans
    (_root_.ISize.toInt_toBitVec x))

public theorem Int8.toInt_bmod_two_pow_numBits : type_of% @_root_.Int8.toInt_bmod_two_pow_numBits := by
  intro x
  rw [← _root_.Int8.toInt_toISize x]
  exact ISize.toInt_bmod_two_pow_numBits _

public theorem Int16.toInt_bmod_two_pow_numBits : type_of% @_root_.Int16.toInt_bmod_two_pow_numBits := by
  intro x
  rw [← _root_.Int16.toInt_toISize x]
  exact ISize.toInt_bmod_two_pow_numBits _

public theorem Int32.toInt_bmod_two_pow_numBits : type_of% @_root_.Int32.toInt_bmod_two_pow_numBits := by
  intro x
  rw [← _root_.Int32.toInt_toISize x]
  exact ISize.toInt_bmod_two_pow_numBits _

public theorem Int8.ofNat_le_iff_le : type_of% @_root_.Int8.ofNat_le_iff_le := by
  intro a b ha hb
  apply _root_.Int8.le_iff_toInt_le.trans
  rw [_root_.Int8.toInt_ofNat_of_lt ha, _root_.Int8.toInt_ofNat_of_lt hb]
  exact Int.ofNat_le

public theorem Int8.ofNat_lt_iff_lt : type_of% @_root_.Int8.ofNat_lt_iff_lt := by
  intro a b ha hb
  apply _root_.Int8.lt_iff_toInt_lt.trans
  rw [_root_.Int8.toInt_ofNat_of_lt ha, _root_.Int8.toInt_ofNat_of_lt hb]
  exact Int.ofNat_lt

public theorem Int16.ofNat_le_iff_le : type_of% @_root_.Int16.ofNat_le_iff_le := by
  intro a b ha hb
  apply _root_.Int16.le_iff_toInt_le.trans
  rw [_root_.Int16.toInt_ofNat_of_lt ha, _root_.Int16.toInt_ofNat_of_lt hb]
  exact Int.ofNat_le

public theorem Int16.ofNat_lt_iff_lt : type_of% @_root_.Int16.ofNat_lt_iff_lt := by
  intro a b ha hb
  apply _root_.Int16.lt_iff_toInt_lt.trans
  rw [_root_.Int16.toInt_ofNat_of_lt ha, _root_.Int16.toInt_ofNat_of_lt hb]
  exact Int.ofNat_lt

public theorem Int16.ofInt_tdiv : type_of% @_root_.Int16.ofInt_tdiv := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int16.minValue.toInt ≤ z) (hi : z ≤ Int16.maxValue.toInt) :
      (Int16.ofInt z).toInt = z := @_root_.Int16.toInt_ofIntLE z lo hi
  apply _root_.Int16.toInt.inj
  rw [_root_.Int16.toInt_ofInt, _root_.Int16.toInt_div, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem Int16.ofInt_tmod : type_of% @_root_.Int16.ofInt_tmod := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int16.minValue.toInt ≤ z) (hi : z ≤ Int16.maxValue.toInt) :
      (Int16.ofInt z).toInt = z := @_root_.Int16.toInt_ofIntLE z lo hi
  apply _root_.Int16.toInt.inj
  rw [_root_.Int16.toInt_ofInt]
  conv => rhs; rw [← _root_.Int16.toInt_bmod_size, _root_.Int16.toInt_mod, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem Int32.ofNat_le_iff_le : type_of% @_root_.Int32.ofNat_le_iff_le := by
  intro a b ha hb
  apply _root_.Int32.le_iff_toInt_le.trans
  rw [_root_.Int32.toInt_ofNat_of_lt ha, _root_.Int32.toInt_ofNat_of_lt hb]
  exact Int.ofNat_le

public theorem Int32.ofNat_lt_iff_lt : type_of% @_root_.Int32.ofNat_lt_iff_lt := by
  intro a b ha hb
  apply _root_.Int32.lt_iff_toInt_lt.trans
  rw [_root_.Int32.toInt_ofNat_of_lt ha, _root_.Int32.toInt_ofNat_of_lt hb]
  exact Int.ofNat_lt

public theorem Int32.ofInt_tdiv : type_of% @_root_.Int32.ofInt_tdiv := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int32.minValue.toInt ≤ z) (hi : z ≤ Int32.maxValue.toInt) :
      (Int32.ofInt z).toInt = z := @_root_.Int32.toInt_ofIntLE z lo hi
  apply _root_.Int32.toInt.inj
  rw [_root_.Int32.toInt_ofInt, _root_.Int32.toInt_div, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem Int32.ofInt_tmod : type_of% @_root_.Int32.ofInt_tmod := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int32.minValue.toInt ≤ z) (hi : z ≤ Int32.maxValue.toInt) :
      (Int32.ofInt z).toInt = z := @_root_.Int32.toInt_ofIntLE z lo hi
  apply _root_.Int32.toInt.inj
  rw [_root_.Int32.toInt_ofInt]
  conv => rhs; rw [← _root_.Int32.toInt_bmod_size, _root_.Int32.toInt_mod, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem Int64.ofNat_le_iff_le : type_of% @_root_.Int64.ofNat_le_iff_le := by
  intro a b ha hb
  apply _root_.Int64.le_iff_toInt_le.trans
  rw [_root_.Int64.toInt_ofNat_of_lt ha, _root_.Int64.toInt_ofNat_of_lt hb]
  exact Int.ofNat_le

public theorem Int64.ofNat_lt_iff_lt : type_of% @_root_.Int64.ofNat_lt_iff_lt := by
  intro a b ha hb
  apply _root_.Int64.lt_iff_toInt_lt.trans
  rw [_root_.Int64.toInt_ofNat_of_lt ha, _root_.Int64.toInt_ofNat_of_lt hb]
  exact Int.ofNat_lt

public theorem Int64.ofInt_tdiv : type_of% @_root_.Int64.ofInt_tdiv := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int64.minValue.toInt ≤ z) (hi : z ≤ Int64.maxValue.toInt) :
      (Int64.ofInt z).toInt = z := @_root_.Int64.toInt_ofIntLE z lo hi
  apply _root_.Int64.toInt.inj
  rw [_root_.Int64.toInt_ofInt, _root_.Int64.toInt_div, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem Int64.ofInt_tmod : type_of% @_root_.Int64.ofInt_tmod := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : Int64.minValue.toInt ≤ z) (hi : z ≤ Int64.maxValue.toInt) :
      (Int64.ofInt z).toInt = z := @_root_.Int64.toInt_ofIntLE z lo hi
  apply _root_.Int64.toInt.inj
  rw [_root_.Int64.toInt_ofInt]
  conv => rhs; rw [← _root_.Int64.toInt_bmod_size, _root_.Int64.toInt_mod, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem ISize.ofNat_le_iff_le : type_of% @_root_.ISize.ofNat_le_iff_le := by
  intro a b ha hb
  apply _root_.ISize.le_iff_toInt_le.trans
  rw [_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits ha, _root_.ISize.toInt_ofNat_of_lt_two_pow_numBits hb]
  exact Int.ofNat_le

public theorem ISize.ofNat_lt_iff_lt : type_of% @_root_.ISize.ofNat_lt_iff_lt := by
  intro a b ha hb
  apply _root_.ISize.lt_iff_toInt_lt.trans
  rw [_root_.ISize.toInt_ofNat_of_lt_two_pow_numBits ha, _root_.ISize.toInt_ofNat_of_lt_two_pow_numBits hb]
  exact Int.ofNat_lt

public theorem ISize.ofInt_tdiv : type_of% @_root_.ISize.ofInt_tdiv := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : ISize.minValue.toInt ≤ z) (hi : z ≤ ISize.maxValue.toInt) :
      (ISize.ofInt z).toInt = z := @_root_.ISize.toInt_ofIntLE z lo hi
  apply _root_.ISize.toInt.inj
  rw [_root_.ISize.toInt_ofInt, _root_.ISize.toInt_div, repr a ha₁ ha₂, repr b hb₁ hb₂]

public theorem ISize.ofInt_tmod : type_of% @_root_.ISize.ofInt_tmod := by
  intro a b ha₁ ha₂ hb₁ hb₂
  have repr (z : Int) (lo : ISize.minValue.toInt ≤ z) (hi : z ≤ ISize.maxValue.toInt) :
      (ISize.ofInt z).toInt = z := @_root_.ISize.toInt_ofIntLE z lo hi
  apply _root_.ISize.toInt.inj
  rw [_root_.ISize.toInt_ofInt]
  conv => rhs; rw [← _root_.ISize.toInt_bmod_size, _root_.ISize.toInt_mod, repr a ha₁ ha₂, repr b hb₁ hb₂]

end OmegaChecks.InitPort.Alternatives
