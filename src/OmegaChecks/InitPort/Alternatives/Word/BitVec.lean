module

public import Init.Data.SInt.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public def BitVec.flattenListFast : type_of% @_root_.BitVec.flattenListFast :=
  @_root_.BitVec.flattenList

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

end OmegaChecks.InitPort.Alternatives
