module

public import OmegaChecks.InitPort.Alternatives.Word.Index

namespace OmegaChecks.InitPort.Alternatives

public theorem BitVec.sub_toNat_mod_cancel_of_toNat : type_of% @_root_.BitVec.sub_toNat_mod_cancel_of_toNat :=
  fun h => Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos _) (Nat.pos_of_ne_zero h))

public theorem BitVec.toNat_lt_of_msb_false : type_of% @_root_.BitVec.toNat_lt_of_msb_false := by
  intro w x h
  exact Nat.lt_of_not_ge (of_decide_eq_false ((@_root_.BitVec.msb_eq_decide w x).symm.trans h))

public theorem BitVec.lt_of_msb_false_of_msb_true : type_of% @_root_.BitVec.lt_of_msb_false_of_msb_true := by
  intro w x y hx hy
  exact Nat.lt_of_lt_of_le (BitVec.toNat_lt_of_msb_false hx) (_root_.BitVec.le_toNat_of_msb_true hy)

public theorem BitVec.toNat_div_toNat_lt : type_of% @_root_.BitVec.toNat_div_toNat_lt := by
  intro w x y
  exact Nat.lt_of_le_of_lt (Nat.div_le_self ..) x.isLt

public theorem BitVec.not_allOnes_lt : type_of% @_root_.BitVec.not_allOnes_lt := by
  intro w x
  apply Nat.not_lt_of_ge
  change x.toNat ≤ (_root_.BitVec.allOnes w).toNat
  rw [_root_.BitVec.toNat_allOnes]
  exact Nat.le_sub_one_of_lt x.isLt

public theorem BitVec.allOnes_le_iff : type_of% @_root_.BitVec.allOnes_le_iff := by
  intro w x
  exact ⟨fun h => _root_.BitVec.le_antisymm (_root_.BitVec.not_lt.mp BitVec.not_allOnes_lt) h,
    fun h => _root_.BitVec.le_of_eq h.symm⟩

public theorem BitVec.lt_allOnes_iff : type_of% @_root_.BitVec.lt_allOnes_iff := by
  intro w x
  exact _root_.BitVec.not_le.symm.trans (not_congr BitVec.allOnes_le_iff)

public theorem BitVec.ne_not_self : type_of% @_root_.BitVec.ne_not_self := by
  intro w a h e
  have bit := congrArg (fun v : BitVec w => v[0]) e
  change a[0] = (~~~a)[0] at bit
  rw [_root_.BitVec.getElem_not] at bit
  cases atZero : a[0] <;> rw [atZero] at bit <;> exact Bool.noConfusion bit

public theorem BitVec.not_self_ne : type_of% @_root_.BitVec.not_self_ne :=
  fun h eq => BitVec.ne_not_self h eq.symm

public theorem BitVec.neg_ne_iff_ne_neg : type_of% @_root_.BitVec.neg_ne_iff_ne_neg := by
  intro w x y
  exact not_congr _root_.BitVec.neg_eq_iff_eq_neg

public theorem BitVec.neg_ne_intMin_inj : type_of% @_root_.BitVec.neg_ne_intMin_inj := by
  intro w x
  exact not_congr _root_.BitVec.neg_eq_intMin

public theorem BitVec.sle_eq_slt_or_eq : type_of% @_root_.BitVec.sle_eq_slt_or_eq := by
  intro w x y
  apply Bool.eq_iff_iff.mpr
  exact _root_.BitVec.sle_iff_toInt_le.trans (Int.le_iff_lt_or_eq.trans ((or_congr
    _root_.BitVec.slt_iff_toInt_lt.symm (_root_.BitVec.toInt_inj.trans beq_iff_eq.symm)).trans
    Bool.or_eq_true_iff.symm))

public theorem BitVec.slt_eq_sle_and_ne : type_of% @_root_.BitVec.slt_eq_sle_and_ne := by
  intro w x y
  apply Bool.eq_iff_iff.mpr
  exact _root_.BitVec.slt_iff_toInt_lt.trans (Int.lt_iff_le_and_ne.trans ((and_congr
    _root_.BitVec.sle_iff_toInt_le.symm ((not_congr _root_.BitVec.toInt_inj).trans bne_iff_ne.symm)).trans
    Bool.and_eq_true_iff.symm))

private theorem signed_exact {w : Nat} (hw : 0 < w) (n : Int)
    (h : ¬ ((decide (2^(w-1) ≤ n)) || decide (n < -2^(w-1))) = true) :
    n.bmod (2^w) = n := by
  rw [← _root_.BitVec.toInt_ofInt]
  exact _root_.BitVec.toInt_ofInt_eq_self hw
    (Int.le_of_not_gt (fun lt => h (Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true lt)))))
    (Int.lt_of_not_ge (fun le => h (Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true le)))))

public theorem BitVec.toInt_add_of_not_saddOverflow : type_of% @_root_.BitVec.toInt_add_of_not_saddOverflow := by
  intro w x y h
  cases w with
  | zero => rw [_root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length]; rfl
  | succ w =>
    rw [_root_.BitVec.toInt_add]
    exact signed_exact (Nat.zero_lt_succ w) _ h

public theorem BitVec.saddOverflow_assoc : type_of% @_root_.BitVec.saddOverflow_assoc := by
  intro w x y z hx hy
  unfold _root_.BitVec.saddOverflow
  rw [BitVec.toInt_add_of_not_saddOverflow hx, BitVec.toInt_add_of_not_saddOverflow hy, Int.add_assoc]

public theorem BitVec.toInt_sub_of_not_ssubOverflow : type_of% @_root_.BitVec.toInt_sub_of_not_ssubOverflow := by
  intro w x y h
  cases w with
  | zero => rw [_root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length]; rfl
  | succ w =>
    rw [_root_.BitVec.toInt_sub]
    exact signed_exact (Nat.zero_lt_succ w) _ h

public theorem BitVec.toInt_mul_of_not_smulOverflow : type_of% @_root_.BitVec.toInt_mul_of_not_smulOverflow := by
  intro w x y h
  cases w with
  | zero => rw [_root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length, _root_.BitVec.toInt_zero_length]; rfl
  | succ w =>
    rw [_root_.BitVec.toInt_mul]
    exact signed_exact (Nat.zero_lt_succ w) _ h

public theorem BitVec.smulOverflow_assoc : type_of% @_root_.BitVec.smulOverflow_assoc := by
  intro w x y z hx hy
  unfold _root_.BitVec.smulOverflow
  rw [BitVec.toInt_mul_of_not_smulOverflow hx, BitVec.toInt_mul_of_not_smulOverflow hy, Int.mul_assoc]

end OmegaChecks.InitPort.Alternatives
