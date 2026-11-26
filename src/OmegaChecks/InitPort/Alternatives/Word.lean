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

end OmegaChecks.InitPort.Alternatives
