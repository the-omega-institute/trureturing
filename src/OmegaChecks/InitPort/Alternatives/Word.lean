module

public import Init.Data.SInt.Lemmas

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

public theorem Nat.one_mod_two_pow_eq_one : type_of% @_root_.Nat.one_mod_two_pow_eq_one := by
  intro n
  cases n with
  | zero => exact ⟨fun h => Nat.noConfusion h, fun h => False.elim (Nat.lt_irrefl 0 h)⟩
  | succ n => exact ⟨fun _ => Nat.zero_lt_succ n,
      fun _ => Nat.mod_eq_of_lt (Nat.one_lt_two_pow n.succ_ne_zero)⟩

public theorem BitVec.toNat_one : type_of% @_root_.BitVec.toNat_one := by
  intro w hw
  exact (_root_.BitVec.toNat_ofNat 1 w).trans
    (Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hw)))

public theorem BitVec.toNat_neg_of_pos : type_of% @_root_.BitVec.toNat_neg_of_pos := by
  intro w x h
  exact (_root_.BitVec.toNat_neg x).trans
    (Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) h))

public theorem BitVec.neg_one_eq_allOnes : type_of% @_root_.BitVec.neg_one_eq_allOnes := by
  intro w
  cases w with
  | zero => rfl
  | succ k =>
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_neg, _root_.BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow k.succ_ne_zero),
      _root_.BitVec.toNat_allOnes, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)]

public theorem BitVec.toNat_twoPow : type_of% @_root_.BitVec.toNat_twoPow := by
  intro w i
  rw [_root_.BitVec.twoPow, _root_.BitVec.toNat_shiftLeft, _root_.BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.one_mul]

public theorem Nat.pow_pred_lt_pow : type_of% @_root_.Nat.pow_pred_lt_pow :=
  fun hx hw => Nat.pow_lt_pow_of_lt hx (Nat.sub_one_lt_of_lt hw)

public theorem Nat.two_pow_pred_lt_two_pow : type_of% @_root_.Nat.two_pow_pred_lt_two_pow :=
  fun h => Nat.pow_lt_pow_of_lt Nat.one_lt_two (Nat.sub_one_lt_of_lt h)

public theorem Nat.two_pow_pred_mod_two_pow : type_of% @_root_.Nat.two_pow_pred_mod_two_pow :=
  fun h => Nat.mod_eq_of_lt (Nat.pow_lt_pow_of_lt Nat.one_lt_two (Nat.sub_one_lt_of_lt h))

public theorem Nat.two_pow_pred_add_two_pow_pred : type_of% @_root_.Nat.two_pow_pred_add_two_pow_pred :=
  fun h => (Nat.mul_two _).symm.trans (Nat.two_pow_pred_mul_two h)

public theorem Int.two_pow_pred_sub_two_pow : type_of% @_root_.Int.two_pow_pred_sub_two_pow := by
  intro w h
  rw [← Nat.two_pow_pred_add_two_pow_pred h, Int.natCast_add, ← Int.sub_sub, Int.sub_self, Int.zero_sub]

public theorem BitVec.toNat_sub_of_le : type_of% @_root_.BitVec.toNat_sub_of_le := by
  intro w x y h
  rw [_root_.BitVec.toNat_sub, ← Nat.sub_add_comm (Nat.le_of_lt y.isLt), Nat.add_sub_assoc h,
    Nat.add_mod_left, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..) x.isLt)]

public theorem BitVec.toNat_intMin : type_of% @_root_.BitVec.toNat_intMin :=
  fun {w} => BitVec.toNat_twoPow w (w - 1)

public theorem BitVec.toNat_intMin_of_pos : type_of% @_root_.BitVec.toNat_intMin_of_pos :=
  fun h => BitVec.toNat_intMin.trans (Nat.mod_eq_of_lt (Nat.two_pow_pred_lt_two_pow h))

public theorem BitVec.toNat_intMax : type_of% @_root_.BitVec.toNat_intMax := by
  intro w
  cases w with
  | zero => rfl
  | succ k =>
    have hi := _root_.BitVec.toNat_intMin_of_pos (Nat.zero_lt_succ k)
    have one := BitVec.toNat_one (Nat.zero_lt_succ k)
    change (_root_.BitVec.intMin (k + 1) - 1#(k + 1)).toNat = _
    have le : 1#(k + 1) ≤ _root_.BitVec.intMin (k + 1) := by
      change (1#(k + 1)).toNat ≤ (_root_.BitVec.intMin (k + 1)).toNat
      rw [one, hi]
      exact Nat.two_pow_pos _
    rw [BitVec.toNat_sub_of_le le, one, hi]

public theorem BitVec.toInt_intMin_of_pos : type_of% @_root_.BitVec.toInt_intMin_of_pos := by
  intro w h
  have half := _root_.BitVec.toNat_intMin_of_pos h
  have boundary : ¬2 * 2 ^ (w - 1) < 2 ^ w := by
    rw [Nat.two_mul, Nat.two_pow_pred_add_two_pow_pred h]
    exact Nat.lt_irrefl _
  rw [_root_.BitVec.toInt, half, ite_eq_right boundary, Int.two_pow_pred_sub_two_pow h,
    Int.natCast_pow, Int.cast_ofNat_Int]

public theorem BitVec.toInt_intMin : type_of% @_root_.BitVec.toInt_intMin := by
  intro w
  cases w with
  | zero => rfl
  | succ k =>
    have h := Nat.zero_lt_succ k
    rw [BitVec.toInt_intMin_of_pos h, Nat.two_pow_pred_mod_two_pow h, Int.natCast_pow, Int.cast_ofNat_Int]

public theorem BitVec.intMin_eq_zero_iff : type_of% @_root_.BitVec.intMin_eq_zero_iff := by
  intro w
  cases w with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ k =>
    have pos : 0 < (_root_.BitVec.intMin (k + 1)).toNat := by
      rw [BitVec.toNat_intMin_of_pos (Nat.zero_lt_succ k)]
      exact Nat.two_pow_pos _
    exact ⟨fun h => False.elim (Nat.ne_of_gt pos
      ((congrArg _root_.BitVec.toNat h).trans _root_.BitVec.toNat_zero)),
      fun h => False.elim (k.succ_ne_zero h)⟩

public theorem BitVec.toInt_intMax : type_of% @_root_.BitVec.toInt_intMax := by
  intro w
  cases w with
  | zero => rfl
  | succ k =>
    have fits : 2 * (2 ^ k - 1) < 2 ^ (k + 1) := by
      rw [Nat.pow_succ']
      exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)
        (Nat.zero_lt_succ 1)
    rw [_root_.BitVec.toInt, BitVec.toNat_intMax, Nat.add_one_sub_one, ite_eq_left fits, Int.ofNat_sub Nat.one_le_two_pow,
      Int.natCast_pow, Int.cast_ofNat_Int, Int.cast_ofNat_Int]

public theorem Nat.two_pow_sub_two_pow_pred : type_of% @_root_.Nat.two_pow_sub_two_pow_pred := by
  intro w h
  rw [← Nat.two_pow_pred_add_two_pow_pred h, Nat.add_sub_cancel]

public theorem BitVec.neg_intMin : type_of% @_root_.BitVec.neg_intMin := by
  intro w
  cases w with
  | zero => rfl
  | succ k =>
    have h := Nat.zero_lt_succ k
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_neg, BitVec.toNat_intMin_of_pos h, Nat.two_pow_sub_two_pow_pred h,
      Nat.two_pow_pred_mod_two_pow h]

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

public theorem BitVec.toInt_signExtend_of_le : type_of% @_root_.BitVec.toInt_signExtend_of_le := by
  intro w v x h
  cases v with
  | zero =>
    have zero := Nat.eq_zero_of_le_zero h
    subst w
    rw [_root_.BitVec.eq_nil x]
    rfl
  | succ v =>
    have bound : (2 : Int) ^ (w-1) ≤ 2 ^ (v+1-1) := Int.ofNat_le.mpr
      (Nat.pow_le_pow_right (Nat.zero_lt_two) (Nat.sub_le_sub_right h 1))
    exact _root_.BitVec.toInt_ofInt_eq_self (Nat.zero_lt_succ v)
      (Int.le_trans (Int.neg_le_neg bound) (_root_.BitVec.le_toInt x))
      (Int.lt_of_lt_of_le (_root_.BitVec.toInt_lt (x := x)) bound)

public theorem BitVec.toInt_signExtend_eq_toInt_bmod_of_le :
    type_of% @_root_.BitVec.toInt_signExtend_eq_toInt_bmod_of_le :=
  fun _ _ => _root_.BitVec.toInt_ofInt _

public theorem BitVec.toInt_signExtend_eq_toNat_bmod_of_le :
    type_of% @_root_.BitVec.toInt_signExtend_eq_toNat_bmod_of_le := by
  intro w v x hv
  rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le x hv, _root_.BitVec.toInt_eq_toNat_bmod,
    Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow _ hv)]

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

public theorem BitVec.setWidth_neg_of_le : type_of% @_root_.BitVec.setWidth_neg_of_le := by
  intro v w x h
  apply (_root_.BitVec.add_right_inj (x.setWidth w)).mp
  rw [← _root_.BitVec.setWidth_add x (-x) h, _root_.BitVec.add_right_neg, _root_.BitVec.setWidth_zero,
    _root_.BitVec.add_right_neg]

public theorem BitVec.signExtend_eq_setWidth_of_le : type_of% @_root_.BitVec.signExtend_eq_setWidth_of_le := by
  intro w x v hv
  apply _root_.BitVec.eq_of_toInt_eq
  exact (BitVec.toInt_signExtend_eq_toNat_bmod_of_le hv).trans (_root_.BitVec.toInt_setWidth x).symm

public theorem BitVec.signExtend_neg_of_le : type_of% @_root_.BitVec.signExtend_neg_of_le := by
  intro v w h b
  rw [BitVec.signExtend_eq_setWidth_of_le _ h, BitVec.signExtend_eq_setWidth_of_le _ h,
    BitVec.setWidth_neg_of_le h]

public theorem BitVec.toInt_neg_of_ne_intMin : type_of% @_root_.BitVec.toInt_neg_of_ne_intMin := by
  intro w x nonmin
  cases w with
  | zero => exact False.elim (nonmin ((_root_.BitVec.eq_nil x).trans (_root_.BitVec.eq_nil _).symm))
  | succ w =>
    apply _root_.BitVec.toInt_neg_of_not_negOverflow
    intro h
    have e : x.toInt = -(2 : Int) ^ ((w+1)-1) := eq_of_beq h
    exact nonmin (_root_.BitVec.eq_of_toInt_eq (e.trans (_root_.BitVec.toInt_intMin_of_pos (Nat.zero_lt_succ w)).symm))

public theorem BitVec.signExtend_neg_of_ne_intMin : type_of% @_root_.BitVec.signExtend_neg_of_ne_intMin := by
  intro v w b nonmin
  change _root_.BitVec.ofInt w (-b).toInt = -_root_.BitVec.ofInt w b.toInt
  rw [BitVec.toInt_neg_of_ne_intMin nonmin, _root_.BitVec.ofInt_neg]

public theorem BitVec.getLsbD_last : type_of% @_root_.BitVec.getLsbD_last := by
  intro w x
  cases w with
  | zero => rw [_root_.BitVec.eq_nil x]; rfl
  | succ w =>
    change x.toNat.testBit w = decide (2 ^ w ≤ x.toNat)
    by_cases large : 2 ^ w ≤ x.toNat
    · rw [decide_eq_true large]
      exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt large x.isLt
    · rw [decide_eq_false large]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_not_ge large)

public theorem BitVec.msb_eq_false_iff_two_mul_lt : type_of% @_root_.BitVec.msb_eq_false_iff_two_mul_lt := by
  intro w x
  cases w with
  | zero => rw [_root_.BitVec.eq_nil x]; decide
  | succ w =>
    rw [_root_.BitVec.msb_eq_decide]
    change decide (2 ^ w ≤ x.toNat) = false ↔ 2*x.toNat < 2^(w+1)
    rw [Nat.pow_succ]
    constructor
    · intro eq
      exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge (of_decide_eq_false eq)) Nat.zero_lt_two)
        (Nat.mul_comm _ _)
    · intro lt
      apply decide_eq_false
      intro high
      rw [Nat.mul_comm (2^w)] at lt
      exact Nat.not_le_of_gt lt (Nat.mul_le_mul_left 2 high)

public theorem BitVec.msb_eq_true_iff_two_mul_ge : type_of% @_root_.BitVec.msb_eq_true_iff_two_mul_ge := by
  intro w x
  constructor
  · intro yes
    apply Nat.le_of_not_gt
    intro small
    exact Bool.noConfusion (yes.symm.trans (BitVec.msb_eq_false_iff_two_mul_lt.mpr small))
  · intro large
    cases h : x.msb with
    | true => rfl
    | false => exact False.elim (Nat.not_lt_of_ge large (BitVec.msb_eq_false_iff_two_mul_lt.mp h))

public theorem BitVec.toInt_eq_msb_cond : type_of% @_root_.BitVec.toInt_eq_msb_cond := by
  intro w x
  cases h : x.msb with
  | true =>
    rw [_root_.BitVec.toInt, ite_eq_right (Nat.not_lt_of_ge (BitVec.msb_eq_true_iff_two_mul_ge.mp h))]
    rfl
  | false =>
    rw [_root_.BitVec.toInt, ite_eq_left (BitVec.msb_eq_false_iff_two_mul_lt.mp h)]
    rfl

end OmegaChecks.InitPort.Alternatives
