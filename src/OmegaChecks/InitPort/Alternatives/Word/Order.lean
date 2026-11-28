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

public theorem BitVec.slt_zero_iff_msb_cond : type_of% @_root_.BitVec.slt_zero_iff_msb_cond := by
  intro w x
  apply _root_.BitVec.slt_iff_toInt_lt.trans
  rw [_root_.BitVec.toInt_zero]
  exact _root_.BitVec.toInt_neg_iff.trans _root_.BitVec.msb_eq_true_iff_two_mul_ge.symm

public theorem BitVec.slt_zero_eq_msb : type_of% @_root_.BitVec.slt_zero_eq_msb := by
  intro w x
  exact Bool.eq_iff_iff.mpr BitVec.slt_zero_iff_msb_cond

public theorem BitVec.sdiv_self : type_of% @_root_.BitVec.sdiv_self := by
  intro w x
  if zero : x = 0#w then
    rw [ite_eq_left (beq_iff_eq.mpr zero), zero, _root_.BitVec.sdiv_zero]
  else
    rw [ite_eq_right (fun h => zero (eq_of_beq h))]
    rw [_root_.BitVec.sdiv_eq]
    cases sign : x.msb with
    | false => exact _root_.BitVec.udiv_self.trans (ite_eq_right (fun eq => zero (eq_of_beq eq)))
    | true => exact _root_.BitVec.udiv_self.trans (ite_eq_right (fun eq =>
        zero (_root_.BitVec.neg_eq_zero_iff.mp (eq_of_beq eq))))

public theorem BitVec.toFin_srem : type_of% @_root_.BitVec.toFin_srem := by
  intro w x y
  rw [_root_.BitVec.srem_eq]
  cases hx : x.msb <;> cases hy : y.msb <;> rfl

public theorem BitVec.intMin_le_iff_msb_eq_true : type_of% @_root_.BitVec.intMin_le_iff_msb_eq_true := by
  intro w x pos
  apply _root_.BitVec.le_def.trans
  rw [_root_.BitVec.toNat_intMin_of_pos pos]
  exact decide_eq_true_iff.symm.trans ((@_root_.BitVec.msb_eq_decide w x).symm ▸ Iff.rfl)

public theorem BitVec.neg_le_intMin_of_msb_eq_true : type_of% @_root_.BitVec.neg_le_intMin_of_msb_eq_true := by
  intro w x sign
  cases w with
  | zero => exact _root_.BitVec.le_of_zero_length rfl
  | succ w =>
    apply _root_.BitVec.le_def.mpr
    rw [_root_.BitVec.toNat_neg_of_pos (_root_.BitVec.pos_of_msb sign), _root_.BitVec.toNat_intMin_of_pos (Nat.zero_lt_succ w)]
    have lower := _root_.BitVec.le_toNat_of_msb_true sign
    change 2^w ≤ x.toNat at lower
    change 2^(w+1)-x.toNat ≤ 2^w
    rw [Nat.pow_succ, Nat.mul_two]
    omega

public theorem BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add : type_of% @_root_.BitVec.toNat_shiftLeft_or_toNat_lt_two_pow_add := by
  intro m n x y
  rw [← _root_.BitVec.toNat_append]
  exact (x ++ y).isLt

public theorem BitVec.toFin_append : type_of% @_root_.BitVec.toFin_append := by
  intro m n x y
  exact Fin.eq_of_val_eq (_root_.BitVec.toNat_append ..)

public theorem BitVec.toNat_signExtend : type_of% @_root_.BitVec.toNat_signExtend := by
  intro w x v
  if narrower : v ≤ w then
    rw [_root_.BitVec.signExtend_eq_setWidth_of_le _ narrower,
      Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right Nat.zero_lt_two narrower)]
    cases x.msb <;> exact (Nat.add_zero _).symm
  else
    have bound := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two (Nat.le_of_not_ge narrower)
    cases sign : x.msb with
    | false =>
      rw [_root_.BitVec.signExtend_eq_setWidth_of_msb_false sign]
      exact (Nat.add_zero _).symm
    | true =>
      rw [_root_.BitVec.signExtend_eq_not_setWidth_not_of_msb_true sign, _root_.BitVec.toNat_not,
        _root_.BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (~~~x).isLt bound),
        _root_.BitVec.toNat_not, _root_.BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt bound)]
      have fit := x.isLt
      change 2^v-1-(2^w-1-x.toNat) = x.toNat+(2^v-2^w)
      omega

public theorem BitVec.toFin_signExtend : type_of% @_root_.BitVec.toFin_signExtend := by
  intro w v x
  apply Fin.eq_of_val_eq
  rw [_root_.BitVec.val_toFin, BitVec.toNat_signExtend, _root_.BitVec.toNat_setWidth, Fin.val_ofNat]
  if narrower : v ≤ w then
    rw [Nat.sub_eq_zero_of_le (Nat.pow_le_pow_right Nat.zero_lt_two narrower)]
    cases x.msb <;> simp only [ite_self, Nat.add_zero]
  else
    have le := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two (Nat.le_of_not_ge narrower)
    have fit := x.isLt
    have bounded := Nat.lt_of_lt_of_le fit le
    rw [Nat.mod_eq_of_lt bounded]
    cases x.msb with
    | false => exact (Nat.mod_eq_of_lt (show x.toNat+0 < 2^v by omega)).symm
    | true => exact (Nat.mod_eq_of_lt (show x.toNat+(2^v-2^w) < 2^v by omega)).symm

public theorem BitVec.toInt_append : type_of% @_root_.BitVec.toInt_append := by
  intro n m x y
  if nz : n = 0 then
    subst n
    rw [ite_eq_left (beq_iff_eq.mpr rfl), _root_.BitVec.append_of_zero_width x y rfl]
    have castInt {a b : Nat} (h : a = b) (v : BitVec a) : (v.cast h).toInt = v.toInt := by cases h; rfl
    exact castInt _ _
  else
    rw [ite_eq_right (fun h => nz (eq_of_beq h))]
    have val : ((x ++ y).toNat : Int) = 2^m*(x.toNat : Int)+y.toNat := by
      rw [_root_.BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq,
        Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.mul_comm]
      rfl
    rw [_root_.BitVec.toInt_eq_msb_cond, BitVec.msb_append, ite_eq_right nz, val, _root_.BitVec.toInt_eq_msb_cond]
    cases x.msb with
    | false => rfl
    | true =>
      change _ - ((2^(n+m) : Nat) : Int) = _ * (_ - ((2^n : Nat) : Int)) + _
      rw [Nat.pow_add, Int.natCast_mul, Int.natCast_pow, Int.natCast_pow, Int.mul_sub]
      change _ - (2 : Int)^n * 2^m = 2^m * (x.toNat : Int) - 2^m * 2^n + y.toNat
      rw [Int.mul_comm ((2 : Int)^n) (2^m)]
      omega

public theorem BitVec.toInt_append_zero : type_of% @_root_.BitVec.toInt_append_zero := by
  intro n m x
  rw [BitVec.toInt_append, _root_.BitVec.toNat_zero, Int.ofNat_zero, Int.add_zero]
  if empty : n = 0 then
    rw [ite_eq_left (beq_iff_eq.mpr empty), _root_.BitVec.toInt_zero, _root_.BitVec.toInt_of_zero_length empty,
      Int.mul_zero]
  else rw [ite_eq_right (fun h => empty (eq_of_beq h))]

public theorem BitVec.toInt_zero_append : type_of% @_root_.BitVec.toInt_zero_append := by
  intro n m x
  rw [BitVec.toInt_append, _root_.BitVec.toInt_zero, Int.mul_zero, Int.zero_add]
  if empty : m = 0 then rw [ite_eq_left empty, ite_eq_left (beq_iff_eq.mpr empty)]
  else rw [ite_eq_right empty, ite_eq_right (fun h => empty (eq_of_beq h))]

public theorem BitVec.toInt_shiftLeftZeroExtend : type_of% @_root_.BitVec.toInt_shiftLeftZeroExtend := by
  intro w n x
  have equals : x.shiftLeftZeroExtend n = x ++ 0#n := by
    apply _root_.BitVec.eq_of_toNat_eq
    rw [_root_.BitVec.toNat_shiftLeftZeroExtend, _root_.BitVec.toNat_append, _root_.BitVec.toNat_zero,
      Nat.or_zero]
  rw [equals, BitVec.toInt_append_zero, Int.mul_comm]

public theorem BitVec.neg_one_ediv_toInt_eq : type_of% @_root_.BitVec.neg_one_ediv_toInt_eq := by
  intro w y
  rw [Int.neg_one_ediv]
  if zero : y.toInt = 0 then rw [ite_eq_left zero, zero]; rfl
  else
    rw [ite_eq_right zero]
    if pos : 0 < y.toInt then rw [ite_eq_left pos, Int.sign_eq_one_of_pos pos]
    else rw [ite_eq_right pos, Int.sign_eq_neg_one_of_neg (show y.toInt < 0 by omega)]; rfl

public theorem BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one :
    type_of% @_root_.BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one := by
  intro w x y hx hy
  have lower := _root_.BitVec.le_toInt x
  have denominator := _root_.BitVec.le_toInt y
  if zero : x.toInt = 0 then rw [zero, Int.zero_ediv]; omega
  else if negOne : x.toInt = -1 then
    rw [negOne, BitVec.neg_one_ediv_toInt_eq, ite_eq_right (show y.toInt ≠ 0 by omega),
      ite_eq_right (show ¬ 0 < y.toInt by omega)]
    omega
  else
    have bound := Int.ediv_lt_natAbs_self_of_lt_neg_one_of_lt_neg_one (show x.toInt < -1 by omega) hy
    omega

end OmegaChecks.InitPort.Alternatives
