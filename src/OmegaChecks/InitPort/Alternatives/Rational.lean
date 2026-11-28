module

public import Init.Data.Rat.Lemmas
public import Init.Data.Dyadic.Inv
import all Init.Data.Dyadic.Round
import all Init.Data.Dyadic.Basic

namespace OmegaChecks.InitPort.Alternatives

public theorem Rat.normalize_eq_zero : type_of% @_root_.Rat.normalize_eq_zero := by
  intro d n hd
  have eq := _root_.Rat.normalize_eq_iff (n₁ := n) (n₂ := 0) hd Nat.one_ne_zero
  rw [Rat.normalize_zero, Int.zero_mul, Int.cast_ofNat_Int, Int.mul_one] at eq
  exact eq

public theorem Rat.mkRat_eq_zero : type_of% @_root_.Rat.mkRat_eq_zero := by
  intro d n hd
  rw [← Rat.normalize_eq_mkRat hd]
  exact Rat.normalize_eq_zero hd

public theorem Rat.den_divInt : type_of% @_root_.Rat.den_divInt := by
  intro a b
  cases b with
  | ofNat n =>
    change (mkRat a n).den = _
    rw [Rat.den_mkRat]
    cases n with
    | zero => rfl
    | succ k =>
      rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (show Int.ofNat (k+1) ≠ 0 by intro h; cases h)]
      rfl
  | negSucc n =>
    change (mkRat (-a) (n+1)).den = _
    rw [Rat.den_mkRat, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Int.negSucc_ne_zero _),
      Int.natAbs_neg]
    rfl

public theorem Rat.add_le_add_left : type_of% @_root_.Rat.add_le_add_left := by
  intro a b c
  have diff : (c + b) - (c + a) = b - a := by
    apply Rat.add_right_cancel (c + a)
    rw [Rat.sub_add_cancel, Rat.add_left_comm, Rat.sub_add_cancel]
  exact (Rat.le_iff_sub_nonneg ..).trans (diff ▸ (Rat.le_iff_sub_nonneg a b).symm)

public theorem Rat.add_le_add_right : type_of% @_root_.Rat.add_le_add_right := by
  intro a b c
  rw [Rat.add_comm a c, Rat.add_comm b c]
  exact Rat.add_le_add_left

public theorem Rat.add_lt_add_left : type_of% @_root_.Rat.add_lt_add_left := by
  intro a b c
  exact Rat.not_le.symm.trans ((not_congr Rat.add_le_add_left).trans Rat.not_le)

public theorem Rat.add_lt_add_right : type_of% @_root_.Rat.add_lt_add_right := by
  intro a b c
  exact Rat.not_le.symm.trans ((not_congr Rat.add_le_add_right).trans Rat.not_le)

public theorem Rat.add_le_iff_le_sub : type_of% @_root_.Rat.add_le_iff_le_sub := by
  intro a b c
  have order := Rat.add_le_add_right (a := a) (b := c-b) (c := b)
  rw [Rat.sub_add_cancel] at order
  exact order

public theorem Rat.le_add_iff_sub_le : type_of% @_root_.Rat.le_add_iff_sub_le := by
  intro a b c
  have order := Rat.add_le_add_right (a := a-c) (b := b) (c := c)
  rw [Rat.sub_add_cancel] at order
  exact order

public theorem Rat.lt_sub_right_iff_add_lt : type_of% @_root_.Rat.lt_sub_right_iff_add_lt := by
  intro a b c
  have order := (Rat.add_lt_add_right (a := a) (b := c-b) (c := b)).symm
  rw [Rat.sub_add_cancel] at order
  exact order

public theorem Rat.sub_lt_iff : type_of% @_root_.Rat.sub_lt_iff := by
  intro a b c
  have order := (Rat.add_lt_add_right (a := a-c) (b := b) (c := c)).symm
  rw [Rat.sub_add_cancel] at order
  exact order

public theorem Rat.floor_add_le_floor_add_intCast : type_of% @_root_.Rat.floor_add_le_floor_add_intCast := by
  intro x y
  apply Rat.le_floor_iff.mpr
  rw [Rat.intCast_add]
  exact Rat.add_le_add_right.mpr (Rat.floor_le x)

public theorem Rat.floor_add_intCast : type_of% @_root_.Rat.floor_add_intCast := by
  intro x y
  apply Int.le_antisymm
  · have lower := Rat.floor_add_le_floor_add_intCast (x := x + y) (y := -y)
    rw [Rat.intCast_neg, ← Rat.sub_eq_add_neg, Rat.add_sub_cancel] at lower
    omega
  · exact Rat.floor_add_le_floor_add_intCast

public theorem Rat.lt_floor : type_of% @_root_.Rat.lt_floor := by
  intro x
  apply Rat.floor_lt_iff.mp
  rw [Rat.floor_sub_one]
  omega

public theorem Rat.ceil_lt : type_of% @_root_.Rat.ceil_lt := by
  intro x
  have bound := Rat.lt_floor (x := -x)
  rw [Rat.ceil_eq_neg_floor_neg, Rat.intCast_neg]
  apply Rat.neg_lt_iff.mpr
  rw [Rat.neg_add, ← Rat.sub_eq_add_neg]
  exact bound

open _root_.Dyadic

public theorem Dyadic.eq_toDyadic_of_precision_le :
    type_of% @_root_.Dyadic.eq_toDyadic_of_precision_le := by
  intro q y prec hp lower upper
  have pos : (0 : Rat) < 2 ^ prec := Rat.zpow_pos (by decide)
  have nz := Rat.ne_of_gt pos
  have cast := congrArg _root_.Dyadic.toRat
    ((toDyadic_toRat y prec).trans (roundDown_eq_self_of_le hp))
  rw [Rat.toRat_toDyadic] at cast
  have scaled := congrArg (· * (2 : Rat) ^ prec) cast.symm
  change y.toRat * 2 ^ prec = ((y.toRat * 2 ^ prec).floor : Rat) / 2 ^ prec * 2 ^ prec at scaled
  rw [Rat.div_mul_cancel nz] at scaled
  have hi := Rat.mul_lt_mul_of_pos_right upper pos
  rw [Rat.add_mul, Rat.zpow_neg, Rat.inv_mul_cancel _ nz] at hi
  have floors : (q * 2 ^ prec).floor = (y.toRat * 2 ^ prec).floor := by
    apply Int.le_antisymm
    · apply Int.lt_add_one_iff.mp
      apply Rat.floor_lt_iff.mpr
      rw [Rat.intCast_add, Rat.intCast_one, ← scaled]
      exact hi
    · apply Rat.le_floor_iff.mpr
      rw [← scaled]
      exact Rat.mul_le_mul_of_nonneg_right lower (Rat.le_of_lt pos)
  apply toRat_inj.mp
  rw [Rat.toRat_toDyadic, floors]
  exact cast.symm

public theorem Dyadic.divAtPrec_mul_le : type_of% @_root_.Dyadic.divAtPrec_mul_le := by
  intro a b hb prec
  have pos := toRat_lt_toRat_iff.mpr hb
  rw [toRat_zero] at pos
  apply toRat_le_toRat_iff.mp
  rw [toRat_mul]
  cases b with
  | zero => exact False.elim (Rat.lt_irrefl pos)
  | ofOdd n k hn =>
    exact (Rat.div_mul_cancel (a := a.toRat) (Rat.ne_of_gt pos)) ▸
      Rat.mul_le_mul_of_nonneg_right Rat.toRat_toDyadic_le (Rat.le_of_lt pos)

public theorem Dyadic.lt_divAtPrec_add_inc_mul : type_of% @_root_.Dyadic.lt_divAtPrec_add_inc_mul := by
  intro a b hb prec
  have pos := toRat_lt_toRat_iff.mpr hb
  rw [toRat_zero] at pos
  apply toRat_lt_toRat_iff.mp
  rw [toRat_mul]
  cases b with
  | zero => exact False.elim (Rat.lt_irrefl pos)
  | ofOdd n k hn =>
    exact (Rat.div_mul_cancel (a := a.toRat) (Rat.ne_of_gt pos)) ▸
      Rat.mul_lt_mul_of_pos_right Rat.lt_toRat_toDyadic_add pos

public theorem Dyadic.eq_divAtPrec : type_of% @_root_.Dyadic.eq_divAtPrec := by
  intro a b hb prec y hp lower upper
  have pos := toRat_lt_toRat_iff.mpr hb
  rw [toRat_zero] at pos
  have lowerRat := toRat_le_toRat_iff.mpr lower
  have upperRat := toRat_lt_toRat_iff.mpr upper
  rw [toRat_mul] at lowerRat
  rw [toRat_mul, toRat_add, toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_one,
    Rat.one_mul] at upperRat
  have cancel : a.toRat / b.toRat * b.toRat = a.toRat := Rat.div_mul_cancel (Rat.ne_of_gt pos)
  have le : y.toRat ≤ a.toRat / b.toRat := Rat.le_of_mul_le_mul_right
    (cancel.symm ▸ lowerRat) pos
  have lt : a.toRat / b.toRat < y.toRat + 2 ^ (-prec) := Rat.lt_of_mul_lt_mul_right
    (cancel.symm ▸ upperRat) (Rat.le_of_lt pos)
  cases b with
  | zero => exact False.elim (Rat.lt_irrefl pos)
  | ofOdd n k hn => exact Dyadic.eq_toDyadic_of_precision_le hp le lt

public theorem Dyadic.mul_invAtPrec_lt_divAtPrec_add :
    type_of% @_root_.Dyadic.mul_invAtPrec_lt_divAtPrec_add := by
  intro a b ha hb prec
  have nonneg := toRat_le_toRat_iff.mpr ha
  rw [toRat_zero] at nonneg
  apply toRat_lt_toRat_iff.mp
  rw [toRat_mul]
  cases b with
  | zero => exact False.elim (Rat.lt_irrefl (toRat_lt_toRat_iff.mpr hb))
  | ofOdd n k hn =>
    have lower : a.toRat * ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat
        ≤ a.toRat / (ofOdd n k hn).toRat := by
      rw [Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_left Rat.toRat_toDyadic_le nonneg
    exact Rat.not_le.mp fun h => Rat.not_le.mpr Rat.lt_toRat_toDyadic_add (Rat.le_trans h lower)

public theorem Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec :
    type_of% @_root_.Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec := by
  intro a b ha hb prec
  have pos := toRat_lt_toRat_iff.mpr ha
  rw [toRat_zero] at pos
  apply toRat_lt_toRat_iff.mp
  rw [toRat_sub, toRat_mul, toRat_mul, toRat_ofIntWithPrec_eq_mul_two_pow,
    Rat.intCast_one, Rat.one_mul]
  apply Rat.sub_lt_iff.mpr
  cases b with
  | zero => exact False.elim (Rat.lt_irrefl (toRat_lt_toRat_iff.mpr hb))
  | ofOdd n k hn =>
    have lower : ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec).toRat
        ≤ a.toRat * (ofOdd n k hn).toRat⁻¹ := Rat.toRat_toDyadic_le
    have upper := Rat.mul_lt_mul_of_pos_left
      (Rat.lt_toRat_toDyadic_add (x := (ofOdd n k hn).toRat⁻¹) (prec := prec)) pos
    rw [toRat_add, toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_one,
      Rat.one_mul, Rat.mul_add] at upper
    exact Rat.not_le.mp fun h => Rat.not_le.mpr upper (Rat.le_trans h lower)

public theorem Dyadic.roundDown_le : type_of% @_root_.Dyadic.roundDown_le := by
  intro x prec
  cases x with
  | zero => exact _root_.Dyadic.le_refl _
  | ofOdd n k hn =>
    unfold _root_.Dyadic.roundDown
    dsimp only
    cases h : k - prec with
    | negSucc l => exact _root_.Dyadic.le_refl _
    | ofNat l =>
      apply _root_.Dyadic.toRat_le_toRat_iff.mp
      rw [_root_.Dyadic.ofOdd_eq_ofIntWithPrec, _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
        _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
      have hprec : k = Int.ofNat l + prec := by omega
      rw [hprec, Int.neg_add, Rat.zpow_add (by decide), ← Rat.mul_assoc]
      apply _root_.Rat.mul_le_mul_of_nonneg_right _ (Rat.zpow_nonneg (by decide))
      rw [Int.shiftRight_eq_div_pow]
      apply _root_.Rat.le_of_mul_le_mul_right _ (Rat.zpow_pos (by decide : (0 : Rat) < 2) (n := Int.ofNat l))
      rw [Rat.mul_assoc, ← Rat.zpow_add (by decide), Int.add_left_neg, Rat.zpow_zero, Rat.mul_one]
      have cast : (2 : Rat) ^ (Int.ofNat l) = (2 ^ l : Int) := by
        change (2 : Rat) ^ (l : Int) = (2 ^ l : Int)
        rw [Rat.zpow_natCast, Rat.intCast_pow, Rat.intCast_ofNat]
      rw [cast, ← Rat.intCast_mul]
      exact Rat.intCast_le_intCast.mpr (Int.ediv_mul_le n (Int.pow_ne_zero (by decide : (2 : Int) ≠ 0)))

public theorem Dyadic.le_roundUp : type_of% @_root_.Dyadic.le_roundUp := by
  intro x prec
  rw [_root_.Dyadic.roundUp_eq_neg_roundDown_neg]
  exact Lean.Grind.OrderedAdd.le_neg_iff.mpr Dyadic.roundDown_le

end OmegaChecks.InitPort.Alternatives
