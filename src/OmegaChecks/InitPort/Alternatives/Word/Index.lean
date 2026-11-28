module

public import OmegaChecks.InitPort.Alternatives.Word.BitVec

namespace OmegaChecks.InitPort.Alternatives

private theorem decide_ge_bit (i n : Nat) : decide (n ≤ i) = !decide (i < n) := by
  if h : i < n then
    rw [decide_eq_false (Nat.not_le_of_lt h), decide_eq_true h]
    rfl
  else
    rw [decide_eq_true (Nat.le_of_not_gt h), decide_eq_false h]
    rfl

public theorem BitVec.getLsbD_shiftLeft : type_of% @_root_.BitVec.getLsbD_shiftLeft := by
  intro m i x n
  rw [← _root_.BitVec.testBit_toNat, _root_.BitVec.toNat_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, decide_ge_bit, Bool.and_assoc]
  rfl

public theorem BitVec.getElem_shiftLeft : type_of% @_root_.BitVec.getElem_shiftLeft := by
  intro m i x n hi
  rw [← _root_.BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_shiftLeft, decide_eq_true hi, Bool.true_and]
  rfl

public theorem BitVec.getLsbD_shiftLeftZeroExtend : type_of% @_root_.BitVec.getLsbD_shiftLeftZeroExtend := by
  intro m i x n
  rw [← _root_.BitVec.testBit_toNat, _root_.BitVec.toNat_shiftLeftZeroExtend, Nat.testBit_shiftLeft,
    decide_ge_bit]
  rfl

public theorem BitVec.getLsbD_append : type_of% @_root_.BitVec.getLsbD_append := by
  intro n m i x y
  rw [_root_.BitVec.append_def, _root_.BitVec.getLsbD_or, BitVec.getLsbD_shiftLeftZeroExtend,
    _root_.BitVec.getLsbD_setWidth']
  if h : i < m then
    rw [ite_eq_left h, decide_eq_true h, Bool.not_true, Bool.false_and, Bool.false_or]
  else
    rw [ite_eq_right h, decide_eq_false h, Bool.not_false, Bool.true_and,
      _root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt h), Bool.or_false]

public theorem BitVec.getElem_append : type_of% @_root_.BitVec.getElem_append := by
  intro n m i x y hi
  rw [← _root_.BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_append]
  if h : i < m then rw [ite_eq_left h, dite_eq_left h]; rfl
  else rw [ite_eq_right h, dite_eq_right h]; rfl

public theorem BitVec.getLsbD_one : type_of% @_root_.BitVec.getLsbD_one := by
  intro w i
  rw [_root_.BitVec.getLsbD_ofNat]
  if eq : i = 0 then
    subst i
    rw [decide_eq_true rfl, Nat.testBit_one_eq_true_iff_self_eq_zero.mpr rfl]
  else
    rw [Bool.eq_false_iff.mpr (fun h => eq (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h)),
      decide_eq_false eq, Bool.and_false, Bool.and_false]

public theorem BitVec.getElem_one : type_of% @_root_.BitVec.getElem_one := by
  intro w i hi
  rw [← _root_.BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_one,
    decide_eq_true (Nat.lt_of_le_of_lt (Nat.zero_le _) hi), Bool.true_and]

public theorem BitVec.getLsbD_not : type_of% @_root_.BitVec.getLsbD_not := by
  intro v i x
  if h : i < v then
    rw [decide_eq_true h, Bool.true_and, _root_.BitVec.getLsbD_eq_getElem h,
      _root_.BitVec.getElem_not]
    rfl
  else
    rw [decide_eq_false h, Bool.false_and, _root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt h)]

public theorem BitVec.getMsbD_not : type_of% @_root_.BitVec.getMsbD_not := by
  intro v i x
  rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_not]
  if h : i < v then
    have j : v - 1 - i < v := by omega
    rw [decide_eq_true h, decide_eq_true j, Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and]
  else rw [decide_eq_false h, Bool.false_and, Bool.false_and]

public theorem BitVec.toNat_sshiftRight : type_of% @_root_.BitVec.toNat_sshiftRight := by
  intro w x n
  cases h : x.msb with
  | false => exact _root_.BitVec.toNat_sshiftRight_of_msb_false h
  | true => exact _root_.BitVec.toNat_sshiftRight_of_msb_true h

public theorem BitVec.toFin_sshiftRight_of_msb_false : type_of% @_root_.BitVec.toFin_sshiftRight_of_msb_false := by
  intro w x n hx
  apply Fin.eq_of_val_eq
  change (x.sshiftRight n).toNat = (x.toNat >>> n) % (2^w)
  rw [_root_.BitVec.toNat_sshiftRight_of_msb_false hx, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (Nat.shiftRight_le x.toNat n) x.isLt)]

public theorem BitVec.toFin_sshiftRight_of_msb_true : type_of% @_root_.BitVec.toFin_sshiftRight_of_msb_true := by
  intro w x n hx
  apply Fin.eq_of_val_eq
  rw [_root_.Fin.val_ofNat, _root_.BitVec.val_toFin, _root_.BitVec.toNat_sshiftRight_of_msb_true hx]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..)
    (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one))).symm

public theorem BitVec.getLsbD_sshiftRight : type_of% @_root_.BitVec.getLsbD_sshiftRight := by
  intro w x s i
  if outside : w ≤ i then
    rw [_root_.BitVec.getLsbD_of_ge _ _ outside, decide_eq_true outside, Bool.not_true, Bool.false_and]
  else
    have inside := Nat.lt_of_not_ge outside
    rw [decide_eq_false outside, Bool.not_false, Bool.true_and]
    cases sign : x.msb with
    | false =>
      rw [_root_.BitVec.sshiftRight_eq_of_msb_false sign, _root_.BitVec.getLsbD_ushiftRight]
      if keep : s+i < w then rw [ite_eq_left keep]
      else rw [ite_eq_right keep, _root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt keep)]
    | true =>
      rw [_root_.BitVec.sshiftRight_eq_of_msb_true sign, BitVec.getLsbD_not, _root_.BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_not, decide_eq_true inside, Bool.true_and]
      if keep : s+i < w then rw [ite_eq_left keep, decide_eq_true keep, Bool.true_and, Bool.not_not]
      else rw [ite_eq_right keep, decide_eq_false keep, Bool.false_and, Bool.not_false]

public theorem BitVec.getElem_sshiftRight : type_of% @_root_.BitVec.getElem_sshiftRight := by
  intro w x s i hw
  rw [← _root_.BitVec.getLsbD_eq_getElem hw, BitVec.getLsbD_sshiftRight, decide_eq_false (Nat.not_le_of_lt hw),
    Bool.not_false, Bool.true_and]
  if h : s+i < w then rw [ite_eq_left h, dite_eq_left h]; rfl
  else rw [ite_eq_right h, dite_eq_right h]

public theorem BitVec.getMsbD_one : type_of% @_root_.BitVec.getMsbD_one := by
  intro w i
  rw [_root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_one]
  if inside : i < w then
    have pos := Nat.lt_of_le_of_lt (Nat.zero_le _) inside
    rw [decide_eq_true inside, decide_eq_true pos, Bool.true_and, Bool.true_and, Bool.and_true]
    have atBit : w - 1 - i = 0 ↔ i = w - 1 := by omega
    exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans (atBit.trans decide_eq_true_iff.symm))
  else
    rw [decide_eq_false inside, Bool.false_and]
    if pos : 0 < w then
      have ne : i ≠ w - 1 := by omega
      rw [decide_eq_false ne, Bool.false_and]
    else rw [decide_eq_false pos, Bool.and_false]

public theorem Nat.testBit_two_pow : type_of% @_root_.Nat.testBit_two_pow := by
  intro n m
  rw [← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
  apply Bool.eq_iff_iff.mpr
  apply Bool.and_eq_true_iff.trans
  apply Iff.trans ?_ decide_eq_true_iff.symm
  exact ⟨fun ⟨le, bit⟩ => Nat.le_antisymm (of_decide_eq_true le)
    (Nat.le_of_sub_eq_zero (Nat.testBit_one_eq_true_iff_self_eq_zero.mp bit)),
    fun eq => ⟨decide_eq_true (Nat.le_of_eq eq), Nat.testBit_one_eq_true_iff_self_eq_zero.mpr
      (Nat.sub_eq_zero_of_le (Nat.le_of_eq eq.symm))⟩⟩

public theorem Nat.testBit_two_pow_self : type_of% @_root_.Nat.testBit_two_pow_self := by
  intro n
  exact Nat.testBit_two_pow.trans (decide_eq_true rfl)

public theorem Nat.testBit_two_pow_of_ne : type_of% @_root_.Nat.testBit_two_pow_of_ne := by
  intro n m h
  exact Nat.testBit_two_pow.trans (decide_eq_false h)

public theorem BitVec.getLsbD_twoPow : type_of% @_root_.BitVec.getLsbD_twoPow := by
  intro w i j
  rw [← _root_.BitVec.testBit_toNat]
  if h : i < w then
    rw [_root_.BitVec.toNat_twoPow_of_lt h, Nat.testBit_two_pow, decide_eq_true h, Bool.true_and]
  else
    rw [_root_.BitVec.toNat_twoPow_of_le (Nat.le_of_not_gt h), Nat.zero_testBit,
      decide_eq_false h, Bool.false_and]

public theorem BitVec.getLsbD_signExtend : type_of% @_root_.BitVec.getLsbD_signExtend := by
  intro w x v i
  if inside : i < v then
    rw [decide_eq_true inside, Bool.true_and]
    cases sign : x.msb with
    | false =>
      rw [_root_.BitVec.signExtend_eq_setWidth_of_msb_false sign, _root_.BitVec.getLsbD_setWidth,
        decide_eq_true inside, Bool.true_and]
      if keep : i < w then rw [ite_eq_left keep]
      else rw [ite_eq_right keep, _root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt keep)]
    | true =>
      rw [_root_.BitVec.signExtend_eq_not_setWidth_not_of_msb_true sign, BitVec.getLsbD_not,
        _root_.BitVec.getLsbD_setWidth, BitVec.getLsbD_not, decide_eq_true inside,
        Bool.true_and, Bool.true_and]
      if keep : i < w then rw [ite_eq_left keep, decide_eq_true keep, Bool.true_and, Bool.not_not]
      else rw [ite_eq_right keep, decide_eq_false keep, Bool.false_and, Bool.not_false]
  else
    rw [_root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt inside), decide_eq_false inside, Bool.false_and]

public theorem BitVec.getElem_signExtend : type_of% @_root_.BitVec.getElem_signExtend := by
  intro w x v i inside
  rw [← _root_.BitVec.getLsbD_eq_getElem inside, BitVec.getLsbD_signExtend, decide_eq_true inside, Bool.true_and]
  if keep : i < w then rw [ite_eq_left keep, dite_eq_left keep]; rfl
  else rw [ite_eq_right keep, dite_eq_right keep]

public theorem BitVec.getMsbD_setWidth : type_of% @_root_.BitVec.getMsbD_setWidth := by
  intro n m x i
  rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getLsbD_setWidth, _root_.BitVec.getMsbD_eq_getLsbD]
  if inside : i < m then
    have index : m - 1 - i < m := by omega
    rw [decide_eq_true inside, decide_eq_true index, Bool.true_and, Bool.true_and]
    if inSource : m - n ≤ i then
      have sourceIndex : i + n - m < n := by omega
      rw [decide_eq_true inSource, decide_eq_true sourceIndex, Bool.true_and, Bool.true_and]
      exact congrArg x.getLsbD (by omega)
    else
      have sourceIndex : n ≤ m - 1 - i := by omega
      rw [decide_eq_false inSource, Bool.false_and, _root_.BitVec.getLsbD_of_ge _ _ sourceIndex]
  else
    have sourceIndex : ¬i + n - m < n := by omega
    rw [decide_eq_false inside, decide_eq_false sourceIndex, Bool.false_and, Bool.false_and, Bool.and_false]

public theorem BitVec.getMsbD_shiftLeft : type_of% @_root_.BitVec.getMsbD_shiftLeft := by
  intro w k x i
  rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_shiftLeft]
  if inside : k+i < w then
    have start : k < w := by omega
    have idx : w-1-k < w := by omega
    have offset : ¬ w-1-k < i := by omega
    rw [decide_eq_true start, decide_eq_true inside, decide_eq_true idx, decide_eq_false offset, Bool.not_false,
      Bool.true_and, Bool.true_and, Bool.true_and, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  else
    rw [decide_eq_false inside, Bool.false_and]
    if start : k < w then
      have offset : w-1-k < i := by omega
      rw [decide_eq_true offset, Bool.not_true, Bool.and_false, Bool.false_and, Bool.and_false]
    else rw [decide_eq_false start, Bool.false_and]

public theorem BitVec.getLsbD_reverse : type_of% @_root_.BitVec.getLsbD_reverse := by
  intro w i x
  induction w generalizing i with
  | zero =>
    exact (_root_.BitVec.getLsbD_of_ge _ _ (Nat.zero_le i)).trans
      (_root_.BitVec.getMsbD_of_ge _ _ (Nat.zero_le i)).symm
  | succ w ih =>
    rw [_root_.BitVec.reverse, _root_.BitVec.getLsbD_concat]
    cases i with
    | zero => rfl
    | succ i =>
      rw [ite_eq_right (Nat.succ_ne_zero _), _root_.BitVec.truncate_eq_setWidth, ih, BitVec.getMsbD_setWidth]
      have upper : w - (w + 1) ≤ i := Nat.sub_eq_zero_of_le (Nat.le_succ w) ▸ Nat.zero_le i
      rw [Nat.add_sub_cancel, decide_eq_true upper, Bool.true_and]
      exact congrArg x.getMsbD (by omega)

public theorem BitVec.getMsbD_reverse : type_of% @_root_.BitVec.getMsbD_reverse := by
  intro w i x
  rw [_root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_reverse, _root_.BitVec.getMsbD_eq_getLsbD]
  if inside : i < w then
    have idx : w-1-i < w := by omega
    rw [decide_eq_true inside, decide_eq_true idx, Bool.true_and, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  else
    rw [decide_eq_false inside, Bool.false_and, _root_.BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt inside)]

public theorem BitVec.getMsbD_shiftLeftZeroExtend : type_of% @_root_.BitVec.getMsbD_shiftLeftZeroExtend := by
  intro m i x n
  rw [_root_.BitVec.shiftLeftZeroExtend_eq, BitVec.getMsbD_shiftLeft, BitVec.getMsbD_setWidth,
    decide_eq_true (show m + n - m ≤ i + n by omega), Bool.true_and]
  exact congrArg x.getMsbD (by omega)

public theorem BitVec.msb_shiftLeftZeroExtend : type_of% @_root_.BitVec.msb_shiftLeftZeroExtend :=
  fun x i => BitVec.getMsbD_shiftLeftZeroExtend x i

public theorem BitVec.getMsbD_append : type_of% @_root_.BitVec.getMsbD_append := by
  intro n m i x y
  if back : n ≤ i then
    rw [ite_eq_left back]
    if inside : i < n+m then
      have yi : i-n < m := by omega
      have index : n+m-1-i < m := by omega
      rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getMsbD_eq_getLsbD, decide_eq_true inside,
        decide_eq_true yi, Bool.true_and, Bool.true_and, BitVec.getLsbD_append, ite_eq_left index]
      exact congrArg y.getLsbD (by omega)
    else
      rw [_root_.BitVec.getMsbD_of_ge _ _ (Nat.le_of_not_gt inside),
        _root_.BitVec.getMsbD_of_ge _ _ (show m ≤ i-n by omega)]
  else
    have xi := Nat.lt_of_not_ge back
    have inside : i < n+m := by omega
    have index : ¬n+m-1-i < m := by omega
    rw [ite_eq_right back, _root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getMsbD_eq_getLsbD,
      decide_eq_true inside, decide_eq_true xi, Bool.true_and, Bool.true_and, BitVec.getLsbD_append, ite_eq_right index]
    exact congrArg x.getLsbD (by omega)

public theorem BitVec.msb_append : type_of% @_root_.BitVec.msb_append := by
  intro w v x y
  change (x ++ y).getMsbD 0 = _
  rw [BitVec.getMsbD_append]
  if h : w = 0 then
    subst w
    rw [ite_eq_left (Nat.le_refl 0), ite_eq_left rfl]
    rfl
  else
    rw [ite_eq_right (fun le => h (Nat.eq_zero_of_le_zero le)), ite_eq_right h]
    rfl

public theorem BitVec.getMsbD_ushiftRight : type_of% @_root_.BitVec.getMsbD_ushiftRight := by
  intro w x i n
  if inside : i < w then
    rw [_root_.BitVec.getMsbD_eq_getLsbD, _root_.BitVec.getLsbD_ushiftRight, decide_eq_true inside,
      Bool.true_and, Bool.true_and]
    if fill : i < n then
      rw [decide_eq_true fill, Bool.not_true, Bool.false_and, _root_.BitVec.getLsbD_of_ge _ _ (by omega)]
    else
      rw [decide_eq_false fill, Bool.not_false, Bool.true_and, _root_.BitVec.getMsbD_eq_getLsbD,
        decide_eq_true (show i-n < w by omega), Bool.true_and]
      exact congrArg x.getLsbD (by omega)
  else
    rw [_root_.BitVec.getMsbD_of_ge _ _ (Nat.le_of_not_gt inside), decide_eq_false inside, Bool.false_and]

public theorem BitVec.msb_ushiftRight : type_of% @_root_.BitVec.msb_ushiftRight := by
  intro w x n
  cases n with
  | zero => rw [_root_.BitVec.ushiftRight_zero]; rfl
  | succ n =>
    change (x >>> (n+1)).getMsbD 0 = _
    rw [BitVec.getMsbD_ushiftRight, decide_eq_true (Nat.zero_lt_succ n), Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_and]

public theorem BitVec.getMsbD_sshiftRight : type_of% @_root_.BitVec.getMsbD_sshiftRight := by
  intro w x i n
  if inside : i < w then
    rw [_root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_sshiftRight, decide_eq_true inside,
      Bool.true_and, Bool.true_and, decide_eq_false (show ¬ w ≤ w-1-i by omega), Bool.not_false, Bool.true_and]
    if fill : i < n then
      rw [ite_eq_left fill, ite_eq_right (show ¬n+(w-1-i) < w by omega)]
    else
      rw [ite_eq_right fill, ite_eq_left (show n+(w-1-i) < w by omega), _root_.BitVec.getMsbD_eq_getLsbD,
        decide_eq_true (show i-n < w by omega), Bool.true_and]
      exact congrArg x.getLsbD (by omega)
  else rw [_root_.BitVec.getMsbD_of_ge _ _ (Nat.le_of_not_gt inside), decide_eq_false inside, Bool.false_and]

public theorem BitVec.getElem?_eq_none_iff : type_of% @_root_.BitVec.getElem?_eq_none_iff := by
  intro w n x
  rw [_root_.BitVec.getElem?_eq]
  if inRange : n < w then
    rw [dite_eq_left inRange]
    exact ⟨fun eq => False.elim (Option.some_ne_none _ eq), fun ge => False.elim (Nat.not_le_of_lt inRange ge)⟩
  else
    rw [dite_eq_right inRange]
    exact ⟨fun _ => Nat.le_of_not_gt inRange, fun _ => rfl⟩

public theorem BitVec.none_eq_getElem?_iff : type_of% @_root_.BitVec.none_eq_getElem?_iff := by
  intro w n x
  exact eq_comm.trans BitVec.getElem?_eq_none_iff

public theorem BitVec.getMsb?_of_ge : type_of% @_root_.BitVec.getMsb?_of_ge := by
  intro w x i ge
  rw [_root_.BitVec.getMsb?_eq_getLsb?, ite_eq_right (Nat.not_lt_of_ge ge)]

public theorem BitVec.eq_of_getMsbD_eq : type_of% @_root_.BitVec.eq_of_getMsbD_eq := by
  intro w x y h
  apply _root_.BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [_root_.BitVec.getLsbD_eq_getMsbD, _root_.BitVec.getLsbD_eq_getMsbD, decide_eq_true hi,
    Bool.true_and, Bool.true_and]
  exact h _ (by omega)

public theorem BitVec.getMsbD_setWidth_add : type_of% @_root_.BitVec.getMsbD_setWidth_add := by
  intro w k i x hi
  rw [BitVec.getMsbD_setWidth, decide_eq_true (show w+k-w ≤ i by omega), Bool.true_and]
  exact congrArg x.getMsbD (by omega)

public theorem BitVec.getLsbD_rotateRightAux_of_lt : type_of% @_root_.BitVec.getLsbD_rotateRightAux_of_lt := by
  intro w x r i hi
  rw [_root_.BitVec.rotateRightAux, _root_.BitVec.getLsbD_or, _root_.BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, decide_eq_true hi, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false]

public theorem BitVec.getLsbD_rotateRight_of_lt : type_of% @_root_.BitVec.getLsbD_rotateRight_of_lt := by
  intro w x r i hr
  rw [_root_.BitVec.rotateRight_eq_rotateRightAux_of_lt hr]
  if hi : i < w-r then
    rw [ite_eq_left hi, BitVec.getLsbD_rotateRightAux_of_lt hi]
  else rw [ite_eq_right hi, _root_.BitVec.getLsbD_rotateRightAux_of_ge (Nat.le_of_not_gt hi)]

public theorem BitVec.getLsbD_rotateRight : type_of% @_root_.BitVec.getLsbD_rotateRight := by
  intro w x r i
  cases w with
  | zero =>
    rw [_root_.BitVec.getLsbD_of_ge _ _ (Nat.zero_le i), Nat.zero_sub, ite_eq_right (Nat.not_lt_zero _),
      decide_eq_false (Nat.not_lt_zero i), Bool.false_and]
  | succ w =>
    rw [← _root_.BitVec.rotateRight_mod_eq_rotateRight, BitVec.getLsbD_rotateRight_of_lt (Nat.mod_lt _ (Nat.zero_lt_succ _))]

public theorem BitVec.getElem_rotateRight : type_of% @_root_.BitVec.getElem_rotateRight := by
  intro w x r i hi
  rw [← _root_.BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_rotateRight, decide_eq_true hi, Bool.true_and]
  if head : i < w - r % w then rw [ite_eq_left head, dite_eq_left head]; rfl
  else rw [ite_eq_right head, dite_eq_right head]; rfl

public theorem BitVec.getMsbD_twoPow : type_of% @_root_.BitVec.getMsbD_twoPow := by
  intro i j w
  rw [_root_.BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_twoPow]
  if supported : i < w then
    rw [decide_eq_true supported, Bool.true_and, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    exact Bool.and_eq_true_iff.trans ((and_congr decide_eq_true_iff decide_eq_true_iff).trans
      ((show (j < w ∧ i = w-1-j) ↔ j = w-i-1 by omega).trans decide_eq_true_iff.symm))
  else rw [decide_eq_false supported, Bool.false_and, Bool.false_and, Bool.and_false]

public theorem BitVec.and_twoPow : type_of% @_root_.BitVec.and_twoPow := by
  intro w x i
  apply _root_.BitVec.eq_of_getElem_eq
  intro j hj
  rw [_root_.BitVec.getElem_and, _root_.BitVec.getElem_twoPow]
  if pick : x.getLsbD i = true then
    rw [ite_eq_left pick, _root_.BitVec.getElem_twoPow]
    if eq : j = i then
      subst j
      rw [← _root_.BitVec.getLsbD_eq_getElem hj, pick, Bool.true_and]
    else rw [decide_eq_false eq, Bool.and_false]
  else
    rw [ite_eq_right pick, _root_.BitVec.getElem_zero]
    if eq : j = i then
      subst j
      rw [← _root_.BitVec.getLsbD_eq_getElem hj, Bool.eq_false_iff.mpr pick, Bool.false_and]
    else rw [decide_eq_false eq, Bool.and_false]

public theorem BitVec.cpopNatRec_setWidth_of_le : type_of% @_root_.BitVec.cpopNatRec_setWidth_of_le := by
  intro w pos v acc x bound
  induction pos generalizing acc with
  | zero => rfl
  | succ i ih =>
    rw [_root_.BitVec.cpopNatRec_succ, _root_.BitVec.cpopNatRec_succ, _root_.BitVec.getLsbD_setWidth,
      decide_eq_true (show i < v from bound), Bool.true_and, ih (Nat.le_of_succ_le bound)]

public theorem BitVec.toNat_cpop_setWidth_le_of_le : type_of% @_root_.BitVec.toNat_cpop_setWidth_le_of_le := by
  intro w x n bound
  rw [_root_.BitVec.toNat_cpop, _root_.BitVec.toNat_cpop, BitVec.cpopNatRec_setWidth_of_le _ (Nat.le_refl n)]
  exact _root_.BitVec.cpopNatRec_le_of_pos_le bound

public theorem BitVec.append_extractLsb'_of_lt : type_of% @_root_.BitVec.append_extractLsb'_of_lt := by
  intro len w castEq x
  apply _root_.BitVec.eq_of_getElem_eq
  intro i hi
  rw [_root_.BitVec.getElem_cast, BitVec.getElem_append]
  if low : i < (len-1)*w then
    rw [dite_eq_left low, _root_.BitVec.getElem_extractLsb', Nat.zero_add]
    rfl
  else
    rw [dite_eq_right low, _root_.BitVec.getElem_extractLsb', Nat.add_sub_of_le (Nat.le_of_not_gt low)]
    rfl

public theorem BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false :
    type_of% @_root_.BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_of_getLsbD_false := by
  intro w x i hx
  apply _root_.BitVec.eq_of_getElem_eq
  intro k hk
  simp only [_root_.BitVec.getElem_setWidth, _root_.BitVec.getLsbD_setWidth]
  if eq : k = i then
    subst k
    rw [hx, Bool.and_false, Bool.and_false]
  else
    rw [show decide (k < i+1) = decide (k < i) from
      Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans ((show k < i+1 ↔ k < i by omega).trans decide_eq_true_iff.symm))]

public theorem BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true :
    type_of% @_root_.BitVec.setWidth_setWidth_succ_eq_setWidth_setWidth_or_twoPow_of_getLsbD_true := by
  intro w x i hx
  apply _root_.BitVec.eq_of_getElem_eq
  intro k hk
  simp only [_root_.BitVec.getElem_setWidth, _root_.BitVec.getLsbD_setWidth, _root_.BitVec.getElem_or,
    _root_.BitVec.getElem_twoPow]
  if eq : k = i then
    subst k
    rw [hx, decide_eq_true (Nat.lt_succ_self i), decide_eq_false (Nat.lt_irrefl i), decide_eq_true rfl]
    rfl
  else
    rw [decide_eq_false eq, Bool.or_false, show decide (k < i+1) = decide (k < i) from
      Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans ((show k < i+1 ↔ k < i by omega).trans decide_eq_true_iff.symm))]

end OmegaChecks.InitPort.Alternatives
