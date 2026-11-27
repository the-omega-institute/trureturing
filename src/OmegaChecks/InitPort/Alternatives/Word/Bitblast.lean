module

public import OmegaChecks.InitPort.Alternatives.Word.Order
import all Init.Data.BitVec.Bitblast

namespace OmegaChecks.InitPort.Alternatives

public theorem BitVec.testBit_limit {x i : Nat} (upper : x < 2^(i+1)) :
    x.testBit i = decide (x ≥ 2^i) := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun bit => decide_eq_true (Nat.ge_two_pow_of_testBit bit),
    fun high => Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (of_decide_eq_true high) upper⟩

public theorem BitVec.add_not_self : type_of% @_root_.BitVec.add_not_self := by
  intro w x
  apply _root_.BitVec.eq_of_toNat_eq
  have fit := x.isLt
  have pos := Nat.two_pow_pos w
  rw [_root_.BitVec.toNat_add, _root_.BitVec.toNat_not, _root_.BitVec.toNat_allOnes,
    Nat.add_sub_of_le (show x.toNat ≤ 2^w-1 by omega), Nat.mod_eq_of_lt (by omega)]

public theorem BitVec.adc_spec : type_of% @_root_.BitVec.adc_spec := by
  intro w x y c
  unfold _root_.BitVec.adc
  apply _root_.BitVec.iunfoldr_replace (fun i => _root_.BitVec.carry i x y c) _
  · exact _root_.BitVec.carry_zero
  · intro i
    rw [_root_.BitVec.carry_succ, _root_.BitVec.getElem_add_add_bool i.isLt,
      ← _root_.BitVec.getLsbD_eq_getElem i.isLt, ← _root_.BitVec.getLsbD_eq_getElem i.isLt]
    rfl

public theorem BitVec.add_eq_or_of_and_eq_zero : type_of% @_root_.BitVec.add_eq_or_of_and_eq_zero := by
  intro w x y disjoint
  rw [_root_.BitVec.add_eq_adc, _root_.BitVec.adc,
    _root_.BitVec.iunfoldr_replace (fun _ => false) (x ||| y) false rfl]
  · intro i
    have h := congrArg (fun v : BitVec w => v.getLsbD i) disjoint
    change (x &&& y).getLsbD i = (0#w).getLsbD i at h
    rw [_root_.BitVec.getLsbD_and, _root_.BitVec.getLsbD_zero] at h
    rw [_root_.BitVec.getElem_or, ← _root_.BitVec.getLsbD_eq_getElem i.isLt,
      ← _root_.BitVec.getLsbD_eq_getElem i.isLt]
    cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> first | rfl | rw [hx, hy] at h; contradiction

public theorem BitVec.getElem_umod : type_of% @_root_.BitVec.getElem_umod := by
  intro w i n d hi
  if zero : d = 0#w then rw [ite_eq_left zero, zero, _root_.BitVec.umod_zero]
  else
    rw [ite_eq_right zero, _root_.BitVec.umod_eq_divRec]
    apply _root_.BitVec.lt_def.mpr
    exact Nat.pos_of_ne_zero (fun h => zero (_root_.BitVec.eq_of_toNat_eq h))

public theorem BitVec.getMsbD_umod : type_of% @_root_.BitVec.getMsbD_umod := by
  intro w i n d
  if zero : d = 0#w then rw [ite_eq_left zero, zero, _root_.BitVec.umod_zero]
  else
    rw [ite_eq_right zero, _root_.BitVec.umod_eq_divRec]
    apply _root_.BitVec.lt_def.mpr
    exact Nat.pos_of_ne_zero (fun h => zero (_root_.BitVec.eq_of_toNat_eq h))

public theorem BitVec.carry_succ_one : type_of% @_root_.BitVec.carry_succ_one := by
  intro w i x positive
  induction i with
  | zero =>
    rw [_root_.BitVec.carry_succ, _root_.BitVec.carry_zero, _root_.BitVec.getLsbD_one,
      decide_eq_true positive, decide_eq_true rfl]
    change (x.getLsbD 0 && true || x.getLsbD 0 && false || true && false) = _
    simp only [Bool.and_true, Bool.and_false, Bool.or_false]
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun bit => decide_eq_true (fun j hj => Nat.eq_zero_of_le_zero hj ▸ bit),
      fun all => of_decide_eq_true all 0 (Nat.le_refl 0)⟩
  | succ i ih =>
    rw [_root_.BitVec.carry_succ, ih, _root_.BitVec.getLsbD_one,
      decide_eq_false (Nat.succ_ne_zero i), Bool.and_false, Bool.atLeastTwo_false_mid]
    apply Bool.eq_iff_iff.mpr
    refine Bool.and_eq_true_iff.trans ⟨?_, ?_⟩
    · intro ⟨last, earlier⟩
      refine decide_eq_true fun j hj => ?_
      rcases Nat.le_or_eq_of_le_succ hj with le | eq
      · exact of_decide_eq_true earlier j le
      · exact eq ▸ last
    · intro all
      have bits := of_decide_eq_true all
      exact ⟨bits _ (Nat.le_refl _), decide_eq_true (fun j hj => bits j (Nat.le_succ_of_le hj))⟩

private theorem lowerBits_disjoint (y : BitVec w) (i : Nat) :
    (y.setWidth i).setWidth w &&& _root_.BitVec.twoPow w i = 0#w := by
  rw [BitVec.and_twoPow, _root_.BitVec.getLsbD_setWidth, _root_.BitVec.getLsbD_setWidth,
    decide_eq_false (Nat.lt_irrefl i), Bool.false_and, Bool.and_false]
  rfl

public theorem BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow :
    type_of% @_root_.BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow := by
  intro w x i
  rw [BitVec.and_twoPow]
  if bit : x.getLsbD i = true then
    rw [ite_eq_left bit, BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true bit,
      BitVec.add_eq_or_of_and_eq_zero _ _ (lowerBits_disjoint x i)]
  else
    rw [ite_eq_right bit, _root_.BitVec.add_zero,
      BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false (Bool.eq_false_iff.mpr bit)]

public theorem BitVec.mulRec_eq_mul_signExtend_setWidth : type_of% @_root_.BitVec.mulRec_eq_mul_signExtend_setWidth := by
  intro w x y s
  induction s with
  | zero =>
    rw [_root_.BitVec.mulRec_zero_eq, _root_.BitVec.setWidth_one]
    cases bit : y.getLsbD 0 with
    | true =>
      change x = x * (1#1).setWidth w
      rw [_root_.BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (v := 1) (by decide), _root_.BitVec.mul_one]
    | false =>
      change 0#w = x * (0#1).setWidth w
      rw [_root_.BitVec.setWidth_zero, _root_.BitVec.mul_zero]
  | succ i ih =>
    rw [_root_.BitVec.mulRec_succ_eq, ih, BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_add_twoPow y (i+1),
      _root_.BitVec.mul_add, BitVec.and_twoPow]
    cases bit : y.getLsbD (i+1) with
    | true => exact congrArg (_ + ·) (_root_.BitVec.shiftLeft_eq_mul_twoPow x _)
    | false => exact congrArg (_ + ·) (_root_.BitVec.mul_zero (x := x)).symm

public theorem BitVec.getLsbD_mul : type_of% @_root_.BitVec.getLsbD_mul := by
  intro w x y i
  rw [BitVec.mulRec_eq_mul_signExtend_setWidth, _root_.BitVec.setWidth_setWidth_of_le y (Nat.le_succ w),
    _root_.BitVec.setWidth_eq]

public theorem BitVec.getMsbD_mul : type_of% @_root_.BitVec.getMsbD_mul := by
  intro w x y i
  rw [_root_.BitVec.mul_eq_mulRec]

public theorem BitVec.getElem_mul : type_of% @_root_.BitVec.getElem_mul := by
  intro w x y i hi
  rw [_root_.BitVec.mul_eq_mulRec]

public theorem BitVec.bit_not_eq_not : type_of% @_root_.BitVec.bit_not_eq_not := by
  intro w x
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  rw [_root_.BitVec.getElem_not, ← _root_.BitVec.getLsbD_eq_getElem hi]
  exact _root_.BitVec.bit_not_testBit x ⟨i, hi⟩

public theorem BitVec.bit_neg_eq_neg : type_of% @_root_.BitVec.bit_neg_eq_neg := by
  intro w x
  rw [← _root_.BitVec.add_eq_adc, _root_.BitVec.neg_eq_not_add]
  apply congrArg (· + 1#w)
  exact (BitVec.bit_not_eq_not x).symm

public theorem BitVec.sle_eq_carry : type_of% @_root_.BitVec.sle_eq_carry := by
  intro w x y
  rw [_root_.BitVec.sle_eq_not_slt, _root_.BitVec.slt_eq_not_carry]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.msb_neg_of_ne_intMin_of_ne_zero : type_of% @_root_.BitVec.msb_neg_of_ne_intMin_of_ne_zero := by
  intro w x notMin notZero
  have nz : x.toInt ≠ 0 := fun h => notZero (_root_.BitVec.eq_of_toInt_eq (h.trans _root_.BitVec.toInt_zero.symm))
  rw [_root_.BitVec.msb_eq_toInt (x := -x), _root_.BitVec.msb_eq_toInt (x := x),
    _root_.BitVec.toInt_neg_of_ne_intMin notMin]
  if negative : x.toInt < 0 then rw [decide_eq_true negative, decide_eq_false (show ¬ -x.toInt < 0 by omega)]; rfl
  else rw [decide_eq_false negative, decide_eq_true (show -x.toInt < 0 by omega)]; rfl

public theorem BitVec.msb_neg : type_of% @_root_.BitVec.msb_neg := by
  intro w x
  if min : x = _root_.BitVec.intMin w then
    subst x
    rw [_root_.BitVec.neg_intMin, bne_self_eq_false, Bool.and_false, Bool.false_xor]
  else if zero : x = 0#w then
    subst x
    rw [_root_.BitVec.neg_zero, bne_self_eq_false, Bool.false_and, Bool.false_xor]
  else
    rw [BitVec.msb_neg_of_ne_intMin_of_ne_zero min zero, bne_iff_ne.mpr zero, bne_iff_ne.mpr min]
    exact (Bool.true_xor _).symm

public theorem BitVec.msb_intMin_umod_neg_of_msb_true : type_of% @_root_.BitVec.msb_intMin_umod_neg_of_msb_true := by
  intro w y sign
  apply _root_.BitVec.msb_umod_of_le_of_ne_zero_of_le _ (fun h => _root_.BitVec.ne_zero_of_msb_true sign (_root_.BitVec.neg_eq_zero_iff.mp h))
  · exact _root_.BitVec.neg_le_intMin_of_msb_eq_true sign
  · exact _root_.BitVec.le_refl _

public theorem BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true : type_of% @_root_.BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true := by
  intro w x y hx hy
  apply _root_.BitVec.msb_umod_of_le_of_ne_zero_of_le (_root_.BitVec.neg_le_intMin_of_msb_eq_true hx)
    (fun h => _root_.BitVec.ne_zero_of_msb_true hy (_root_.BitVec.neg_eq_zero_iff.mp h))
    (_root_.BitVec.neg_le_intMin_of_msb_eq_true hy)

public theorem BitVec.getElem_sdiv : type_of% @_root_.BitVec.getElem_sdiv := by
  intro w i x y hi
  rw [_root_.BitVec.sdiv_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getLsbD_sdiv : type_of% @_root_.BitVec.getLsbD_sdiv := by
  intro w i x y
  rw [_root_.BitVec.sdiv_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getMsbD_sdiv : type_of% @_root_.BitVec.getMsbD_sdiv := by
  intro w i x y
  rw [_root_.BitVec.sdiv_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getElem_srem : type_of% @_root_.BitVec.getElem_srem := by
  intro w i x y hi
  rw [_root_.BitVec.srem_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getLsbD_srem : type_of% @_root_.BitVec.getLsbD_srem := by
  intro w i x y
  rw [_root_.BitVec.srem_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getMsbD_srem : type_of% @_root_.BitVec.getMsbD_srem := by
  intro w i x y
  rw [_root_.BitVec.srem_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getElem_smod : type_of% @_root_.BitVec.getElem_smod := by
  intro w i x y hi
  rw [_root_.BitVec.smod_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getMsbD_smod : type_of% @_root_.BitVec.getMsbD_smod := by
  intro w i x y
  rw [_root_.BitVec.smod_eq]
  cases x.msb <;> cases y.msb <;> rfl

public theorem BitVec.getMsbD_neg : type_of% @_root_.BitVec.getMsbD_neg := by
  intro w i x
  rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getLsbD_neg, _root_.BitVec.getMsbD_eq_getLsbD (x := x)]
  if hi : i < w then
    rw [decide_eq_true hi, Bool.true_and, Bool.true_and, decide_eq_true (show w-1-i < w by omega), Bool.true_and]
    apply congrArg (fun b => x.getLsbD (w-1-i) ^^ b)
    apply Bool.eq_iff_iff.mpr
    refine decide_eq_true_iff.trans ((Iff.intro ?_ ?_).trans decide_eq_true_iff.symm)
    · rintro ⟨j, hj, bit⟩
      refine ⟨w-1-j, by omega, by omega, ?_⟩
      rw [_root_.BitVec.getMsbD_eq_getLsbD, decide_eq_true (show w-1-j < w by omega), Bool.true_and,
        show w-1-(w-1-j) = j by omega]
      exact bit
    · rintro ⟨j, hj, later, bit⟩
      rw [_root_.BitVec.getMsbD_eq_getLsbD, decide_eq_true hj, Bool.true_and] at bit
      exact ⟨w-1-j, by omega, bit⟩
  else
    rw [decide_eq_false hi, Bool.false_and, Bool.false_and,
      decide_eq_false (show ¬ ∃ j < w, i < j ∧ x.getMsbD j = true from fun ⟨_, hj, hij, _⟩ => hi (Nat.lt_trans hij hj))]
    rfl

public theorem BitVec.getLsbD_smod : type_of% @_root_.BitVec.getLsbD_smod := by
  intro w i x y
  rw [_root_.BitVec.smod_eq]
  cases x.msb <;> cases y.msb <;> try rfl
  · change (if x % -y = 0#w then x % -y else x % -y + y).getLsbD i = _
    dsimp only
    if zero : x % -y = 0#w then rw [ite_eq_left zero, ite_eq_left zero, zero, _root_.BitVec.getLsbD_zero]
    else rw [ite_eq_right zero, ite_eq_right zero]
  · change (if -x % y = 0#w then -x % y else y - -x % y).getLsbD i = _
    dsimp only
    if zero : -x % y = 0#w then rw [ite_eq_left zero, ite_eq_left zero, zero, _root_.BitVec.getLsbD_zero]
    else rw [ite_eq_right zero, ite_eq_right zero]

public theorem BitVec.neg_slt_zero : type_of% @_root_.BitVec.neg_slt_zero := by
  intro w pos x
  if min : x = _root_.BitVec.intMin w then
    subst x
    rw [_root_.BitVec.neg_intMin, _root_.BitVec.slt_zero_eq_msb, _root_.BitVec.msb_intMin,
      decide_eq_true pos]
    change true = (decide (_root_.BitVec.intMin w = _root_.BitVec.intMin w) || _)
    rw [decide_eq_true rfl, Bool.true_or]
  else
    change _ = (decide (x = _root_.BitVec.intMin w) || _)
    rw [decide_eq_false min, Bool.false_or, _root_.BitVec.slt_eq_decide,
      _root_.BitVec.slt_eq_decide, _root_.BitVec.toInt_zero, _root_.BitVec.toInt_neg_of_ne_intMin min]
    exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans ((show -x.toInt < 0 ↔ 0 < x.toInt by omega).trans decide_eq_true_iff.symm))

public theorem BitVec.msb_srem : type_of% @_root_.BitVec.msb_srem := by
  intro w x y
  rw [_root_.BitVec.msb_eq_toInt (x := x.srem y), _root_.BitVec.toInt_srem]
  if zero : x.srem y = 0 then
    have hz : x.toInt.tmod y.toInt = 0 :=
      (_root_.BitVec.toInt_srem x y).symm.trans ((congrArg _root_.BitVec.toInt zero).trans _root_.BitVec.toInt_zero)
    rw [hz, decide_eq_false (Int.lt_irrefl 0), decide_eq_false (fun ne => ne zero), Bool.and_false]
  else
    have nz : x.toInt.tmod y.toInt ≠ 0 := fun h =>
      zero (_root_.BitVec.eq_of_toInt_eq ((_root_.BitVec.toInt_srem x y).trans (h.trans _root_.BitVec.toInt_zero.symm)))
    rw [decide_eq_true zero, Bool.and_true]
    cases sign : x.msb with
    | false => exact decide_eq_false (Int.not_lt.mpr (Int.tmod_nonneg _ (_root_.BitVec.toInt_nonneg_of_msb_false sign)))
    | true =>
      have bound := Int.tmod_nonneg y.toInt (Int.neg_nonneg_of_nonpos (Int.le_of_lt (_root_.BitVec.toInt_neg_of_msb_true sign)))
      rw [Int.neg_tmod] at bound
      exact decide_eq_true (by omega)

public theorem BitVec.sdiv_ne_intMin_of_ne_intMin : type_of% @_root_.BitVec.sdiv_ne_intMin_of_ne_intMin := by
  intro w x y different
  have pos : 0 < w := _root_.BitVec.length_pos_of_ne different
  have nonMin (a b : BitVec w) (sa : a.msb = false) : a / b ≠ _root_.BitVec.intMin w :=
    _root_.BitVec.ne_intMin_of_msb_eq_false pos (_root_.BitVec.msb_udiv_eq_false_of sa)
  rw [_root_.BitVec.sdiv_eq]
  cases sx : x.msb with
  | false =>
    cases y.msb with
    | false => exact nonMin x y sx
    | true => exact _root_.BitVec.neg_ne_intMin_inj.mpr (nonMin x (-y) sx)
  | true =>
    have sa := BitVec.msb_neg_of_ne_intMin_of_ne_zero different (_root_.BitVec.ne_zero_of_msb_true sx)
    rw [sx] at sa
    cases y.msb with
    | false => exact _root_.BitVec.neg_ne_intMin_inj.mpr (nonMin (-x) y sa)
    | true => exact nonMin (-x) (-y) sa

public theorem BitVec.toInt_sub_neg_umod : type_of% @_root_.BitVec.toInt_sub_neg_umod := by
  intro w x y sx sy nondiv
  if zero : y = 0#w then
    subst y
    rw [_root_.BitVec.umod_zero, _root_.BitVec.zero_sub, _root_.BitVec.neg_neg, _root_.BitVec.toInt_zero, Int.emod_zero]
  else
    have ypos := _root_.BitVec.toNat_pos_of_ne_zero zero
    have upper := _root_.BitVec.toNat_lt_of_msb_false sy
    have fit := Nat.mod_lt (-x).toNat ypos
    have remSign : (-x % y).msb = false := _root_.BitVec.msb_umod_of_le_of_ne_zero_of_le
      (_root_.BitVec.neg_le_intMin_of_msb_eq_true sx) zero (_root_.BitVec.le_intMin_of_msb_eq_false sy)
    have negDividend := _root_.BitVec.toInt_eq_neg_toNat_neg_of_msb_true sx
    have divisor := _root_.BitVec.toInt_eq_toNat_of_msb sy
    rw [divisor, negDividend] at nondiv
    have notDvd : ¬(y.toNat : Int) ∣ ((-x).toNat : Int) := fun h => nondiv (Int.dvd_neg.mpr h)
    rw [_root_.BitVec.toInt_sub, _root_.BitVec.toInt_eq_toNat_of_msb remSign, _root_.BitVec.toNat_umod,
      divisor, negDividend, Int.neg_emod, ite_eq_right notDvd, Int.natAbs_natCast, ← Int.natCast_emod]
    cases w with
    | zero => exact (zero (_root_.BitVec.of_length_zero)).elim
    | succ v =>
      apply Int.bmod_eq_of_le
      all_goals rw [Nat.pow_succ]
      all_goals change y.toNat < 2^v at upper
      all_goals omega

public theorem BitVec.toInt_smod : type_of% @_root_.BitVec.toInt_smod := by
  intro w x y
  if zero : y = 0#w then
    subst y
    rw [_root_.BitVec.smod_zero, _root_.BitVec.toInt_zero, Int.fmod_zero]
  else
    rw [_root_.BitVec.smod_eq]
    cases sx : x.msb <;> cases sy : y.msb <;> dsimp only
    · rw [_root_.BitVec.umod_eq, _root_.BitVec.toInt_umod_of_msb sx,
        Int.fmod_eq_emod_of_nonneg _ (_root_.BitVec.toInt_nonneg_of_msb_false sy),
        _root_.BitVec.toInt_eq_toNat_of_msb sx, _root_.BitVec.toInt_eq_toNat_of_msb sy]
    · rw [_root_.BitVec.umod_eq]
      have div := _root_.BitVec.toInt_dvd_toInt_iff_of_msb_false_msb_true sx sy
      if divides : y.toInt ∣ x.toInt then
        rw [ite_eq_left (div.mp divides), div.mp divides, _root_.BitVec.toInt_zero,
          Int.fmod_eq_zero_of_dvd divides]
      else
        rw [ite_eq_right (fun z => divides (div.mpr z)), _root_.BitVec.toInt_umod_neg_add sy sx divides,
          Int.fmod_eq_emod, ite_eq_right (show ¬ (0 ≤ y.toInt ∨ y.toInt ∣ x.toInt) from fun h =>
            h.elim (Int.not_le_of_gt (_root_.BitVec.toInt_neg_of_msb_true sy)) divides)]
    · rw [_root_.BitVec.umod_eq]
      have div := _root_.BitVec.toInt_dvd_toInt_iff_of_msb_true_msb_false sx sy
      if divides : y.toInt ∣ x.toInt then
        rw [ite_eq_left (div.mp divides), div.mp divides, _root_.BitVec.toInt_zero,
          Int.fmod_eq_zero_of_dvd divides]
      else
        rw [ite_eq_right (fun z => divides (div.mpr z)), BitVec.toInt_sub_neg_umod sx sy divides,
          Int.fmod_eq_emod_of_nonneg _ (_root_.BitVec.toInt_nonneg_of_msb_false sy)]
    · rw [_root_.BitVec.umod_eq, _root_.BitVec.toInt_neg_eq_of_msb (BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true sx sy),
        _root_.BitVec.toInt_eq_toNat_of_msb (BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true sx sy),
        _root_.BitVec.toNat_umod, _root_.BitVec.toInt_eq_neg_toNat_neg_of_msb_true sx,
        _root_.BitVec.toInt_eq_neg_toNat_neg_of_msb_true sy, Int.neg_fmod_neg, Int.fmod_eq_emod_of_nonneg _ (Int.natCast_nonneg _)]
      rfl

public theorem BitVec.msb_smod : type_of% @_root_.BitVec.msb_smod := by
  intro w x y
  apply Bool.or_eq_true_iff.mpr
  if zero : y = 0 then
    subst y
    apply Or.inl (decide_eq_true ?_)
    change (x.smod 0#w).msb = (x.msb && decide ((0 : BitVec w) = 0))
    rw [_root_.BitVec.smod_zero, decide_eq_true rfl, Bool.and_true]
  else
    rw [decide_eq_false zero, Bool.and_false]
    if remZero : x.smod y = 0 then
      exact Or.inl (decide_eq_true ((congrArg _root_.BitVec.msb remZero).trans _root_.BitVec.msb_zero))
    else
      cases sy : y.msb with
      | true => exact Or.inr (Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true remZero⟩)
      | false =>
        have nz : y.toInt ≠ 0 := fun h => zero (_root_.BitVec.eq_of_toInt_eq (h.trans _root_.BitVec.toInt_zero.symm))
        have hy := _root_.BitVec.toInt_nonneg_of_msb_false sy
        apply Or.inl (decide_eq_true ?_)
        rw [_root_.BitVec.msb_eq_toInt, BitVec.toInt_smod]
        exact decide_eq_false (Int.not_lt.mpr (Int.fmod_nonneg_of_pos _ (show 0 < y.toInt by omega)))

end OmegaChecks.InitPort.Alternatives
