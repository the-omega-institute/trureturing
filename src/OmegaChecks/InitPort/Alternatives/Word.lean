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

public theorem BitVec.toInt_eq_toNat_of_msb : type_of% @_root_.BitVec.toInt_eq_toNat_of_msb := by
  intro w x h
  rw [BitVec.toInt_eq_msb_cond, ite_eq_right (fun yes => Bool.noConfusion (h.symm.trans yes))]

public theorem BitVec.pos_of_msb : type_of% @_root_.BitVec.pos_of_msb := by
  intro w x hx
  change 0 < x.toNat
  exact Nat.lt_of_lt_of_le (Nat.two_pow_pos _) (of_decide_eq_true ((_root_.BitVec.msb_eq_decide x).symm.trans hx))

public theorem BitVec.sub_toNat_mod_cancel_of_msb_true : type_of% @_root_.BitVec.sub_toNat_mod_cancel_of_msb_true :=
  fun hx => Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) (BitVec.pos_of_msb hx))

public theorem BitVec.toInt_udiv_of_msb : type_of% @_root_.BitVec.toInt_udiv_of_msb := by
  intro w x hx y
  have small := BitVec.msb_eq_false_iff_two_mul_lt.mp hx
  have divSmall := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.div_le_self x.toNat y.toNat)) small
  rw [_root_.BitVec.toInt_eq_toNat_of_lt (by rw [_root_.BitVec.toNat_udiv]; exact divSmall), _root_.BitVec.toNat_udiv]
  rfl

public theorem BitVec.toInt_eq_neg_toNat_neg_of_msb_true : type_of% @_root_.BitVec.toInt_eq_neg_toNat_neg_of_msb_true := by
  intro w x hx
  rw [BitVec.toInt_eq_msb_cond, ite_eq_left hx, _root_.BitVec.toNat_neg_of_pos (BitVec.pos_of_msb hx),
    Int.natCast_sub (Nat.le_of_lt x.isLt), Int.neg_sub]

public theorem BitVec.toInt_eq_neg_toNat_neg_of_nonpos : type_of% @_root_.BitVec.toInt_eq_neg_toNat_neg_of_nonpos := by
  intro w x hx
  rcases hx with rfl | hx
  · rw [_root_.BitVec.neg_zero, _root_.BitVec.toInt_zero, _root_.BitVec.toNat_zero]
    rfl
  · exact BitVec.toInt_eq_neg_toNat_neg_of_msb_true hx

public theorem BitVec.toInt_sdiv : type_of% @_root_.BitVec.toInt_sdiv := by
  intro w a b
  have div (x y : BitVec w) : x.udiv y = _root_.BitVec.ofInt w ((x.toNat : Int).tdiv (y.toNat : Int)) := by
    apply _root_.BitVec.eq_of_toNat_eq
    change (x / y).toNat = (_root_.BitVec.ofNat w (x.toNat / y.toNat)).toNat
    exact _root_.BitVec.toNat_udiv.trans ((_root_.BitVec.toNat_ofNat _ _).trans
      (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self ..) x.isLt))).symm
  apply Eq.trans _ (_root_.BitVec.toInt_ofInt _)
  apply congrArg _root_.BitVec.toInt
  rw [_root_.BitVec.sdiv_eq]
  cases ha : a.msb <;> cases hb : b.msb
  · rw [BitVec.toInt_eq_toNat_of_msb ha, BitVec.toInt_eq_toNat_of_msb hb]
    exact div a b
  · rw [BitVec.toInt_eq_toNat_of_msb ha, BitVec.toInt_eq_neg_toNat_neg_of_msb_true hb, Int.tdiv_neg, _root_.BitVec.ofInt_neg]
    exact congrArg Neg.neg (div a (-b))
  · rw [BitVec.toInt_eq_neg_toNat_neg_of_msb_true ha, BitVec.toInt_eq_toNat_of_msb hb, Int.neg_tdiv, _root_.BitVec.ofInt_neg]
    exact congrArg Neg.neg (div (-a) b)
  · rw [BitVec.toInt_eq_neg_toNat_neg_of_msb_true ha, BitVec.toInt_eq_neg_toNat_neg_of_msb_true hb, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg]
    exact div (-a) (-b)

public theorem BitVec.toInt_sdiv_of_ne_or_ne : type_of% @_root_.BitVec.toInt_sdiv_of_ne_or_ne := by
  intro w a b h
  cases w with
  | zero => rw [_root_.BitVec.eq_nil a, _root_.BitVec.eq_nil b]; rfl
  | succ w =>
    have hw : 0 < w+1 := Nat.zero_lt_succ w
    have lower := _root_.BitVec.le_toInt a
    have upper := @_root_.BitVec.toInt_lt _ a
    have minval := _root_.BitVec.toInt_intMin_of_pos hw
    have wp : (0 : Int) < 2 ^ ((w+1)-1) := Int.pow_pos (by decide)
    rw [BitVec.toInt_sdiv, ← _root_.BitVec.toInt_ofInt]
    apply _root_.BitVec.toInt_ofInt_eq_self hw
    · have absA := Int.natAbs_eq a.toInt
      have absQ := Int.natAbs_eq (a.toInt.tdiv b.toInt)
      have le := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
      rcases absA with pa | na <;> rcases absQ with pq | nq <;> omega
    · by_cases bz : b.toInt = 0
      · rw [bz, Int.tdiv_zero]
        exact wp
      by_cases bp : b.toInt = 1
      · rw [bp, Int.tdiv_one]
        exact upper
      by_cases bn : b.toInt = -1
      · have bneg : b = -1#(w+1) :=
          _root_.BitVec.ofInt_toInt.symm.trans ((congrArg (_root_.BitVec.ofInt _) bn).trans _root_.BitVec.ofInt_neg)
        have amin : a ≠ _root_.BitVec.intMin _ := h.resolve_right (fun n => n bneg)
        have strict : -2 ^ ((w+1)-1) ≠ a.toInt := fun e => amin (_root_.BitVec.eq_of_toInt_eq (e.symm.trans minval.symm))
        rw [bn, Int.tdiv_neg, Int.tdiv_one]
        omega
      have den : 1 < b.toInt.natAbs := by
        have nonzero := fun e => bz (Int.natAbs_eq_zero.mp e)
        have nonunit : b.toInt.natAbs ≠ 1 := fun e => (Int.natAbs_eq_iff.mp e).elim bp bn
        exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨nonzero, nonunit⟩
      by_cases az : a.toInt = 0
      · rw [az, Int.zero_tdiv]
        exact wp
      have lt := Nat.div_lt_self (Nat.pos_of_ne_zero (fun e => az (Int.natAbs_eq_zero.mp e))) den
      have ltQ : (a.toInt.tdiv b.toInt).natAbs < a.toInt.natAbs := by
        rw [Int.natAbs_tdiv]; exact lt
      have absA := Int.natAbs_eq a.toInt
      have absQ := Int.le_natAbs (a := a.toInt.tdiv b.toInt)
      rcases absA with pa | na <;> omega

public theorem BitVec.mul_one : type_of% @_root_.BitVec.mul_one := by
  intro w x
  cases w with
  | zero => exact (_root_.BitVec.eq_nil _).trans (_root_.BitVec.eq_nil _).symm
  | succ w =>
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_mul, BitVec.toNat_one (Nat.zero_lt_succ w), Nat.mul_one,
      Nat.mod_eq_of_lt x.isLt]

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

public theorem BitVec.toInt_srem : type_of% @_root_.BitVec.toInt_srem := by
  intro w a b
  cases w with
  | zero => rw [_root_.BitVec.eq_nil a, _root_.BitVec.eq_nil b]; rfl
  | succ w =>
    have hw : 0 < w+1 := Nat.zero_lt_succ w
    have rem (x y : BitVec (w+1)) : x % y = _root_.BitVec.ofInt (w+1) ((x.toNat : Int).tmod y.toNat) := by
      apply _root_.BitVec.eq_of_toNat_eq
      change (x % y).toNat = (_root_.BitVec.ofNat (w+1) (x.toNat % y.toNat)).toNat
      exact _root_.BitVec.toNat_umod.trans ((_root_.BitVec.toNat_ofNat _ _).trans
        (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le ..) x.isLt))).symm
    have repr : a.srem b = _root_.BitVec.ofInt (w+1) (a.toInt.tmod b.toInt) := by
      rw [_root_.BitVec.srem_eq]
      cases ha : a.msb <;> cases hb : b.msb
      · rw [BitVec.toInt_eq_toNat_of_msb ha, BitVec.toInt_eq_toNat_of_msb hb]
        exact rem a b
      · rw [BitVec.toInt_eq_toNat_of_msb ha, BitVec.toInt_eq_neg_toNat_neg_of_msb_true hb, Int.tmod_neg]
        exact rem a (-b)
      · rw [BitVec.toInt_eq_neg_toNat_neg_of_msb_true ha, BitVec.toInt_eq_toNat_of_msb hb, Int.neg_tmod, _root_.BitVec.ofInt_neg]
        exact congrArg Neg.neg (rem (-a) b)
      · rw [BitVec.toInt_eq_neg_toNat_neg_of_msb_true ha, BitVec.toInt_eq_neg_toNat_neg_of_msb_true hb, Int.tmod_neg, Int.neg_tmod, _root_.BitVec.ofInt_neg]
        exact congrArg Neg.neg (rem (-a) (-b))
    rw [repr]
    have lo := _root_.BitVec.le_toInt a
    have hi := @_root_.BitVec.toInt_lt _ a
    have pos : (0 : Int) < 2 ^ ((w+1)-1) := Int.pow_pos (by decide)
    have le : (a.toInt.tmod b.toInt).natAbs ≤ a.toInt.natAbs := by
      rw [Int.natAbs_tmod]
      exact Nat.mod_le ..
    apply _root_.BitVec.toInt_ofInt_eq_self hw
    · rcases Int.natAbs_eq a.toInt with pa | na <;> rcases Int.natAbs_eq (a.toInt.tmod b.toInt) with pm | nm <;> omega
    · by_cases ha : 0 ≤ a.toInt
      · have absA := Int.natAbs_of_nonneg ha
        have absM := Int.le_natAbs (a := a.toInt.tmod b.toInt)
        omega
      · have npos := Int.tmod_nonneg b.toInt (Int.neg_nonneg_of_nonpos (Int.le_of_lt (Int.lt_of_not_ge ha)))
        rw [Int.neg_tmod] at npos
        omega

public theorem BitVec.toInt_one_of_lt : type_of% @_root_.BitVec.toInt_one_of_lt := by
  intro w h
  rw [← _root_.BitVec.ofInt_natCast w 1]
  apply _root_.BitVec.toInt_ofInt_eq_self (Nat.zero_lt_of_lt h)
  · have pos : (0 : Int) < 2 ^ (w-1) := Int.pow_pos (by decide)
    omega
  · exact Int.ofNat_lt.mpr (Nat.one_lt_two_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt h)))

public theorem BitVec.sdiv_one : type_of% @_root_.BitVec.sdiv_one := by
  intro w x
  cases w with
  | zero => exact (_root_.BitVec.eq_nil _).trans (_root_.BitVec.eq_nil _).symm
  | succ w => cases w with
    | zero => rcases _root_.BitVec.eq_zero_or_eq_one x with rfl | rfl <;> rfl
    | succ w =>
      apply _root_.BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_sdiv, BitVec.toInt_one_of_lt (Nat.succ_lt_succ (Nat.zero_lt_succ _)), Int.tdiv_one,
        ← _root_.BitVec.toInt_ofInt, _root_.BitVec.ofInt_toInt]

public theorem BitVec.srem_one : type_of% @_root_.BitVec.srem_one := by
  intro w x
  cases w with
  | zero => exact (_root_.BitVec.eq_nil _).trans (_root_.BitVec.eq_nil _).symm
  | succ w => cases w with
    | zero => rcases _root_.BitVec.eq_zero_or_eq_one x with rfl | rfl <;> rfl
    | succ w =>
      apply _root_.BitVec.eq_of_toInt_eq
      rw [BitVec.toInt_srem, BitVec.toInt_one_of_lt (Nat.succ_lt_succ (Nat.zero_lt_succ _)), Int.tmod_one,
        _root_.BitVec.toInt_zero]

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

public theorem BitVec.zero_sle_iff_msb_eq_false : type_of% @_root_.BitVec.zero_sle_iff_msb_eq_false := by
  intro w x
  constructor
  · intro h
    have hx := _root_.BitVec.sle_iff_toInt_le.mp h
    rw [_root_.BitVec.toInt_zero] at hx
    cases hm : x.msb with
    | false => rfl
    | true => exact False.elim (Int.not_lt_of_ge hx (_root_.BitVec.toInt_neg_of_msb_true hm))
  · intro hm
    apply _root_.BitVec.sle_iff_toInt_le.mpr
    rw [_root_.BitVec.toInt_zero]
    exact _root_.BitVec.toInt_nonneg_of_msb_false hm

public theorem BitVec.zero_sle_eq_not_msb : type_of% @_root_.BitVec.zero_sle_eq_not_msb := by
  intro w x
  cases h : x.msb with
  | false => exact BitVec.zero_sle_iff_msb_eq_false.mpr h
  | true =>
    cases hb : _root_.BitVec.sle 0#w x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (h.symm.trans (BitVec.zero_sle_iff_msb_eq_false.mp hb)))

public theorem BitVec.msb_eq_toInt : type_of% @_root_.BitVec.msb_eq_toInt := by
  intro w x
  cases h : x.msb with
  | false => exact (decide_eq_false (Int.not_lt_of_ge (_root_.BitVec.toInt_nonneg_of_msb_false h))).symm
  | true => exact (decide_eq_true (_root_.BitVec.toInt_neg_of_msb_true h)).symm

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

end OmegaChecks.InitPort.Alternatives
