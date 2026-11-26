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

end OmegaChecks.InitPort.Alternatives
