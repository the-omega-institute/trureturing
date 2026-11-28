module

public import OmegaChecks.InitPort.Alternatives.Word.BitVec

namespace OmegaChecks.InitPort.Alternatives

public theorem UInt16.neg_zero : type_of% @_root_.UInt16.neg_zero :=
  _root_.UInt16.toBitVec_inj.mp (BitVec.neg_zero 16)

public theorem UInt32.neg_zero : type_of% @_root_.UInt32.neg_zero :=
  _root_.UInt32.toBitVec_inj.mp (BitVec.neg_zero 32)

public theorem UInt64.neg_zero : type_of% @_root_.UInt64.neg_zero :=
  _root_.UInt64.toBitVec_inj.mp (BitVec.neg_zero 64)

public theorem Int16.neg_zero : type_of% @_root_.Int16.neg_zero :=
  _root_.Int16.toBitVec_inj.mp (BitVec.neg_zero 16)

public theorem Int32.neg_zero : type_of% @_root_.Int32.neg_zero :=
  _root_.Int32.toBitVec_inj.mp (BitVec.neg_zero 32)

public theorem Int64.neg_zero : type_of% @_root_.Int64.neg_zero :=
  _root_.Int64.toBitVec_inj.mp (BitVec.neg_zero 64)

public theorem Int16.toBitVec_minValue : type_of% @_root_.Int16.toBitVec_minValue := by
  change -(32768#16) = _
  have repr : 32768#16 = _root_.BitVec.intMin 16 := by
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_ofNat, BitVec.toNat_intMin]
  exact (congrArg Neg.neg repr).trans BitVec.neg_intMin

public theorem Int16.toInt_minValue : type_of% @_root_.Int16.toInt_minValue :=
  (_root_.Int16.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int16.toBitVec_minValue).trans
      (BitVec.toInt_intMin_of_pos (Nat.zero_lt_succ _)))

public theorem Int32.toBitVec_minValue : type_of% @_root_.Int32.toBitVec_minValue := by
  change -(2147483648#32) = _
  have repr : 2147483648#32 = _root_.BitVec.intMin 32 := by
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_ofNat, BitVec.toNat_intMin]
  exact (congrArg Neg.neg repr).trans BitVec.neg_intMin

public theorem Int32.toInt_minValue : type_of% @_root_.Int32.toInt_minValue :=
  (_root_.Int32.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int32.toBitVec_minValue).trans
      (BitVec.toInt_intMin_of_pos (Nat.zero_lt_succ _)))

public theorem Int64.toBitVec_minValue : type_of% @_root_.Int64.toBitVec_minValue := by
  change -(9223372036854775808#64) = _
  have repr : 9223372036854775808#64 = _root_.BitVec.intMin 64 := by
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_ofNat, BitVec.toNat_intMin]
  exact (congrArg Neg.neg repr).trans BitVec.neg_intMin

public theorem Int64.toInt_minValue : type_of% @_root_.Int64.toInt_minValue :=
  (_root_.Int64.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int64.toBitVec_minValue).trans
      (BitVec.toInt_intMin_of_pos (Nat.zero_lt_succ _)))

public theorem Int16.ofBitVec_intMin : type_of% @_root_.Int16.ofBitVec_intMin :=
  congrArg _root_.Int16.ofBitVec Int16.toBitVec_minValue.symm

public theorem Int16.toInt_minValue_lt_zero : type_of% @_root_.Int16.toInt_minValue_lt_zero := by
  rw [Int16.toInt_minValue]
  apply Int.neg_lt_zero_iff.mpr
  rw [← Int.cast_ofNat_Int (n := 2), ← Int.natCast_pow]
  exact Int.natCast_pos.mpr (Nat.two_pow_pos _)

public theorem Int16.toNatClampNeg_minValue : type_of% @_root_.Int16.toNatClampNeg_minValue :=
  Int.toNat_of_nonpos (Int.le_of_lt Int16.toInt_minValue_lt_zero)

public theorem Int32.ofBitVec_intMin : type_of% @_root_.Int32.ofBitVec_intMin :=
  congrArg _root_.Int32.ofBitVec Int32.toBitVec_minValue.symm

public theorem Int32.toInt_minValue_lt_zero : type_of% @_root_.Int32.toInt_minValue_lt_zero := by
  rw [Int32.toInt_minValue]
  apply Int.neg_lt_zero_iff.mpr
  rw [← Int.cast_ofNat_Int (n := 2), ← Int.natCast_pow]
  exact Int.natCast_pos.mpr (Nat.two_pow_pos _)

public theorem Int32.toNatClampNeg_minValue : type_of% @_root_.Int32.toNatClampNeg_minValue :=
  Int.toNat_of_nonpos (Int.le_of_lt Int32.toInt_minValue_lt_zero)

public theorem Int64.ofBitVec_intMin : type_of% @_root_.Int64.ofBitVec_intMin :=
  congrArg _root_.Int64.ofBitVec Int64.toBitVec_minValue.symm

public theorem Int64.toInt_minValue_lt_zero : type_of% @_root_.Int64.toInt_minValue_lt_zero := by
  rw [Int64.toInt_minValue]
  apply Int.neg_lt_zero_iff.mpr
  rw [← Int.cast_ofNat_Int (n := 2), ← Int.natCast_pow]
  exact Int.natCast_pos.mpr (Nat.two_pow_pos _)

public theorem Int64.toNatClampNeg_minValue : type_of% @_root_.Int64.toNatClampNeg_minValue :=
  Int.toNat_of_nonpos (Int.le_of_lt Int64.toInt_minValue_lt_zero)

/-- The numeral translator writes the low bit after doubling the high part. -/
private def ones (k : Nat) : Nat := Nat.rec 0 (fun _ x => x * 2 + 1) k

private theorem ones_add_one (k : Nat) : ones k + 1 = 2 ^ k :=
  Nat.rec (motive := fun k => ones k + 1 = 2 ^ k) rfl (fun k h => by
    change (ones k * 2 + 1) + 1 = 2 ^ (k + 1)
    rw [Nat.pow_succ, ← h, Nat.add_mul, Nat.one_mul]
  ) k

private theorem ones_eq (k : Nat) : ones k = 2 ^ k - 1 :=
  (Nat.add_sub_cancel (ones k) 1).symm.trans (congrArg (· - 1) (ones_add_one k))

private theorem ones_intMax {w : Nat} (h : 0 < w) :
    _root_.BitVec.ofNat w (ones (w - 1)) = _root_.BitVec.intMax w := by
  have v := ones_eq (w - 1)
  have fits : ones (w - 1) < 2 ^ w := by
    rw [v]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.two_pow_pred_lt_two_pow h)
  apply _root_.BitVec.eq_of_toNat_eq
  exact (_root_.BitVec.toNat_ofNat ..).trans
    ((Nat.mod_eq_of_lt fits).trans (v.trans (@BitVec.toNat_intMax w).symm))

private theorem neg_one_bits (w : Nat) : -1#w = _root_.BitVec.ofNat w (ones w) := by
  have v := ones_eq w
  have fits : ones w < 2 ^ w := by
    rw [v]
    exact Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one
  apply BitVec.neg_one_eq_allOnes.trans
  apply _root_.BitVec.eq_of_toNat_eq
  exact _root_.BitVec.toNat_allOnes.trans
    (v.symm.trans ((Nat.mod_eq_of_lt fits).symm.trans (_root_.BitVec.toNat_ofNat ..).symm))

public theorem UInt16.neg_one_eq : type_of% @_root_.UInt16.neg_one_eq :=
  _root_.UInt16.toBitVec_inj.mp (neg_one_bits 16)

public theorem Int16.toBitVec_maxValue : type_of% @_root_.Int16.toBitVec_maxValue :=
  ones_intMax (Nat.zero_lt_succ 15)

public theorem Int16.ofBitVec_intMax : type_of% @_root_.Int16.ofBitVec_intMax :=
  congrArg _root_.Int16.ofBitVec Int16.toBitVec_maxValue.symm

public theorem Int16.toInt_maxValue : type_of% @_root_.Int16.toInt_maxValue :=
  (_root_.Int16.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int16.toBitVec_maxValue).trans BitVec.toInt_intMax)

public theorem Int16.toInt_maxValue_add_one : type_of% @_root_.Int16.toInt_maxValue_add_one :=
  (congrArg (· + 1) Int16.toInt_maxValue).trans (Int.sub_add_cancel ..)

public theorem UInt32.neg_one_eq : type_of% @_root_.UInt32.neg_one_eq :=
  _root_.UInt32.toBitVec_inj.mp (neg_one_bits 32)

public theorem Int32.toBitVec_maxValue : type_of% @_root_.Int32.toBitVec_maxValue :=
  ones_intMax (Nat.zero_lt_succ 31)

public theorem Int32.ofBitVec_intMax : type_of% @_root_.Int32.ofBitVec_intMax :=
  congrArg _root_.Int32.ofBitVec Int32.toBitVec_maxValue.symm

public theorem Int32.toInt_maxValue : type_of% @_root_.Int32.toInt_maxValue :=
  (_root_.Int32.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int32.toBitVec_maxValue).trans BitVec.toInt_intMax)

public theorem Int32.toInt_maxValue_add_one : type_of% @_root_.Int32.toInt_maxValue_add_one :=
  (congrArg (· + 1) Int32.toInt_maxValue).trans (Int.sub_add_cancel ..)

public theorem UInt64.neg_one_eq : type_of% @_root_.UInt64.neg_one_eq :=
  _root_.UInt64.toBitVec_inj.mp (neg_one_bits 64)

public theorem Int64.toBitVec_maxValue : type_of% @_root_.Int64.toBitVec_maxValue :=
  ones_intMax (Nat.zero_lt_succ 63)

public theorem Int64.ofBitVec_intMax : type_of% @_root_.Int64.ofBitVec_intMax :=
  congrArg _root_.Int64.ofBitVec Int64.toBitVec_maxValue.symm

public theorem Int64.toInt_maxValue : type_of% @_root_.Int64.toInt_maxValue :=
  (_root_.Int64.toInt_toBitVec _).symm.trans
    ((congrArg _root_.BitVec.toInt Int64.toBitVec_maxValue).trans BitVec.toInt_intMax)

public theorem Int64.toInt_maxValue_add_one : type_of% @_root_.Int64.toInt_maxValue_add_one :=
  (congrArg (· + 1) Int64.toInt_maxValue).trans (Int.sub_add_cancel ..)

end OmegaChecks.InitPort.Alternatives
