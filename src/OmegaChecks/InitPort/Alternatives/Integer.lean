module
public import OmegaChecks.InitPort.Alternatives.Integer.Division
public import Init.Data.Int.Pow
public import Init.Data.Int.Cooper
import all Init.Data.Dyadic.Basic
import all Init.Data.Int.Linear

namespace OmegaChecks.InitPort.Alternatives

public theorem Int.lt_asymm : type_of% @_root_.Int.lt_asymm :=
  fun h => Int.not_lt.mpr (Int.le_of_lt h)

public theorem Int.natAbs_eq_iff_mul_eq_zero : type_of% @_root_.Int.natAbs_eq_iff_mul_eq_zero := by
  intro a n
  apply Int.natAbs_eq_iff.trans
  apply Iff.trans ?_ Int.mul_eq_zero.symm
  rw [← Int.sub_neg]
  exact or_congr Int.sub_eq_zero.symm Int.sub_eq_zero.symm

public theorem Int.natAbs_ediv_of_dvd {a b : Int} (hab : b ∣ a) :
    (a / b).natAbs = a.natAbs / b.natAbs := by
  have mul : (a / b).natAbs * b.natAbs = a.natAbs :=
    (_root_.Int.natAbs_mul (a / b) b).symm.trans (congrArg Int.natAbs (Int.ediv_mul_cancel hab))
  cases b with
  | ofNat b =>
    cases b with
    | zero =>
      change (a / 0).natAbs = a.natAbs / 0
      rw [Int.ediv_zero, Nat.div_zero]
      rfl
    | succ b => exact (congrArg (fun x => x / b.succ) mul |>.symm.trans
        (Nat.mul_div_left _ (Nat.succ_pos _))).symm
  | negSucc b => exact (congrArg (fun x => x / b.succ) mul |>.symm.trans
      (Nat.mul_div_left _ (Nat.succ_pos _))).symm

public theorem Int.natAbs_ediv_of_nonneg {a b : Int} (ha : 0 ≤ a) :
    (a / b).natAbs = a.natAbs / b.natAbs := by
  rw [Int.eq_natAbs_of_nonneg ha]
  cases b with
  | ofNat n => rfl
  | negSucc n =>
    exact (congrArg Int.natAbs (_root_.Int.ofNat_ediv_negSucc (a := a.natAbs) (b := n))).trans
      (_root_.Int.natAbs_neg _)

public theorem Int.natAbs_ediv (a b : Int) :
    (a / b).natAbs = a.natAbs / b.natAbs + if 0 ≤ a ∨ b = 0 ∨ b ∣ a then 0 else 1 := by
  by_cases condition : 0 ≤ a ∨ b = 0 ∨ b ∣ a
  · rw [ite_eq_left condition, Nat.add_zero]
    rcases condition with ha | hb | hd
    · exact Int.natAbs_ediv_of_nonneg ha
    · subst b
      rw [Int.ediv_zero]
      exact (Nat.div_zero _).symm
    · exact Int.natAbs_ediv_of_dvd hd
  · rw [ite_eq_right condition]
    cases a with
    | ofNat a => exact False.elim (condition (Or.inl (Int.natCast_nonneg a)))
    | negSucc a =>
      have hd : ¬ b ∣ Int.negSucc a := fun h => condition (Or.inr (Or.inr h))
      cases b with
      | ofNat b =>
        cases b with
        | zero => exact False.elim (condition (Or.inr (Or.inl rfl)))
        | succ b =>
          have rem : (a + 1) % (b + 1) ≠ 0 := fun h =>
            hd (Int.dvd_neg.mpr (Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero h)))
          exact (congrArg Nat.succ (Nat.succ_div_of_mod_ne_zero rem)).symm
      | negSucc b =>
        have rem : (a + 1) % (b + 1) ≠ 0 := fun h =>
          hd (Int.neg_dvd.mpr (Int.dvd_neg.mpr (Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero h))))
        exact (congrArg Nat.succ (Nat.succ_div_of_mod_ne_zero rem)).symm

public theorem Int.tdiv_eq_ediv : type_of% @_root_.Int.tdiv_eq_ediv := by
  intro a b
  cases a with
  | ofNat m =>
    have positive : 0 ≤ Int.ofNat m := Int.natCast_nonneg m
    rw [ite_eq_left (Or.inl positive), Int.add_zero]
    exact Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg m)
  | negSucc m =>
    have neg := Int.not_le_of_gt (Int.negSucc_lt_zero m)
    cases b with
    | ofNat b =>
      cases b with
      | zero =>
        change (Int.negSucc m).tdiv 0 = Int.negSucc m / 0 + ite _ 0 (Int.sign 0)
        rw [Int.tdiv_zero, Int.ediv_zero, Int.sign_zero, ite_self, Int.add_zero]
      | succ n =>
        by_cases hd : Int.ofNat n.succ ∣ Int.negSucc m
        · rw [ite_eq_left (Or.inr hd), Int.add_zero]
          apply Int.neg_ofNat_eq_negSucc_iff.mpr
          exact Nat.succ_div_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd (Int.ofNat_dvd.mp (Int.dvd_neg.mp hd)))
        · rw [ite_eq_right (fun h => h.elim neg hd)]
          have rem : (m+1) % (n+1) ≠ 0 := fun e => hd (Int.dvd_neg.mpr (Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero e)))
          have same := Nat.succ_div_of_mod_ne_zero rem
          change -((m.succ / n.succ : Nat) : Int) = Int.negSucc (m / n.succ) + 1
          rw [same]
          let q := m / n.succ
          change -(q : Int) = -((q : Int) + 1) + 1
          rw [Int.neg_add, Int.add_assoc, Int.add_left_neg, Int.add_zero]
    | negSucc n =>
      by_cases hd : Int.negSucc n ∣ Int.negSucc m
      · rw [ite_eq_left (Or.inr hd), Int.add_zero]
        exact congrArg Int.ofNat (Nat.succ_div_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd
          (Int.ofNat_dvd.mp (Int.dvd_neg.mp (Int.neg_dvd.mp hd)))))
      · rw [ite_eq_right (fun h => h.elim neg hd)]
        have rem : (m+1) % (n+1) ≠ 0 := fun e => hd (Int.neg_dvd.mpr
          (Int.dvd_neg.mpr (Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero e))))
        have same := Nat.succ_div_of_mod_ne_zero rem
        change ((m.succ / n.succ : Nat) : Int) = ((m / n.succ : Nat) : Int) + 1 + -1
        rw [same, Int.add_assoc, Int.add_right_neg, Int.add_zero]

public theorem Int.ediv_eq_tdiv : type_of% @_root_.Int.ediv_eq_tdiv := by
  intro a b
  rw [Int.tdiv_eq_ediv, Int.add_sub_cancel]

public theorem Int.instLawfulBEq : type_of% @_root_.Int.instLawfulBEq where
  rfl := decide_eq_true rfl
  eq_of_beq h := of_decide_eq_true h

public theorem Int.pow_succ : type_of% @_root_.Int.pow_succ := by
  intro m n
  cases m with
  | ofNat a => rfl
  | negSucc a =>
    rw [Int.negSucc_pow, Int.negSucc_pow]
    cases Nat.mod_two_eq_zero_or_one n with
    | inl h =>
      have odd : n.succ % 2 ≠ 0 := fun e =>
        Nat.noConfusion (h.symm.trans (Nat.succ_mod_succ_eq_zero_iff.mp e))
      rw [ite_eq_left h, ite_eq_right odd, Nat.pow_succ]
      rfl
    | inr h =>
      have even : n.succ % 2 = 0 := Nat.succ_mod_succ_eq_zero_iff.mpr h
      have odd : n % 2 ≠ 0 := fun e => Nat.noConfusion (h.symm.trans e)
      rw [ite_eq_left even, ite_eq_right odd, Nat.pow_succ]
      exact (Int.negOfNat_mul_negSucc _ _).symm

public theorem Int.shiftRight_eq_div_pow : type_of% @_root_.Int.shiftRight_eq_div_pow := by
  intro m n
  cases m with
  | ofNat a => exact congrArg Int.ofNat (Nat.shiftRight_eq_div_pow a n)
  | negSucc a =>
    rw [Int.negSucc_ediv a (Int.natCast_pos.mpr (Nat.pow_pos Nat.zero_lt_two))]
    exact congrArg Int.negSucc (Nat.shiftRight_eq_div_pow a n)

public theorem Int.emod_two_eq : type_of% @_root_.Int.emod_two_eq := by
  intro i
  have lo := Int.emod_nonneg i (b := 2) (by decide)
  have hi := Int.emod_lt_of_pos i (b := 2) (by decide)
  cases e : i % 2 with
  | negSucc a =>
    rw [e] at lo
    exact False.elim ((Int.negSucc_not_nonneg a).mp lo)
  | ofNat a =>
    cases a with
    | zero => exact Or.inl rfl
    | succ a =>
      cases a with
      | zero => exact Or.inr rfl
      | succ a =>
        rw [e] at hi
        have bound : a.succ.succ < 2 := Int.ofNat_lt.mp hi
        exact False.elim (Nat.not_lt_zero a (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

public theorem Int.trailingZeros._proof_2 : type_of% @_root_.Int.trailingZeros._proof_2 :=
  fun _ _ hi hk e => hi (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero (e ▸ hk)))

public theorem Int.trailingZeros._proof_4 : type_of% @_root_.Int.trailingZeros._proof_4 :=
  fun _ hi _ _ remainder e =>
    hi ((Int.ediv_mul_cancel_of_emod_eq_zero remainder).symm.trans
        ((congrArg (fun x : Int => x * 2) e).trans (Int.zero_mul 2)))

public theorem Int.trailingZeros._proof_6 : type_of% @_root_.Int.trailingZeros._proof_6 := by
  intro i k bound remainder
  rw [Int.natAbs_ediv_of_dvd (Int.dvd_of_emod_eq_zero remainder)]
  change i.natAbs / 2 ≤ k
  cases Nat.eq_zero_or_pos i.natAbs with
  | inl e => rw [e, Nat.zero_div]; exact Nat.zero_le k
  | inr p =>
    exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.div_lt_self p Nat.one_lt_two) bound)

public theorem Int.shiftRight_trailingZeros_mod_two : type_of% @_root_.Int.shiftRight_trailingZeros_mod_two := by
  intro a ha
  have odd (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat)
      (shifted : a >>> acc = i) : (a >>> _root_.Int.trailingZeros.aux k i hi hk acc) % 2 = 1 := by
    induction k generalizing i acc with
    | zero => exact False.elim (hi (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)))
    | succ k ih =>
      rw [_root_.Int.trailingZeros.aux.eq_1 i hi acc k (Nat.succ_ne_zero k)]
      by_cases even : i % 2 = 0
      · rw [dite_eq_left even]
        apply ih
        exact (Int.shiftRight_add a acc 1).trans ((congrArg (fun x : Int => x >>> 1) shifted).trans
          (Int.shiftRight_eq_div_pow i 1))
      · rw [dite_eq_right even, shifted]
        exact (Int.emod_two_eq i).resolve_left even
  rw [_root_.Int.trailingZeros, dite_eq_right ha]
  exact odd _ a ha (Nat.le_refl _) 0 (Int.shiftRight_zero a)

public theorem Int.ne_iff_lt_or_gt : type_of% @_root_.Int.ne_iff_lt_or_gt := by
  intro a b
  constructor
  · intro ne
    rcases Int.lt_trichotomy a b with h | h | h
    · exact Or.inl h
    · exact False.elim (ne h)
    · exact Or.inr h
  · exact fun h => h.elim Int.ne_of_lt Int.ne_of_gt

public theorem Int.neg_emod_two : type_of% @_root_.Int.neg_emod_two := by
  intro i
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  rw [Int.sub_eq_add_neg, ← Int.two_mul, Int.mul_emod_right]

public theorem Int.natAbs_emod_two : type_of% @_root_.Int.natAbs_emod_two := by
  intro i
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    change n.succ % 2 = ((-(Int.ofNat n.succ)) % 2).natAbs
    rw [Int.neg_emod_two]
    rfl

public theorem Int.shiftLeft_eq : type_of% @_root_.Int.shiftLeft_eq := by
  intro a b
  cases a with
  | ofNat a => exact congrArg Int.ofNat (Nat.shiftLeft_eq a b)
  | negSucc a =>
    change Int.negSucc (((a+1) <<< b) - 1) = -(Int.ofNat (a+1)) * (Int.ofNat (2^b))
    rw [Nat.shiftLeft_eq, Int.neg_mul]
    apply Eq.symm
    apply Int.neg_ofNat_eq_negSucc_iff.mpr
    exact (Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.pow_pos Nat.zero_lt_two))).symm

public theorem Int.trailingZeros_eq_zero_of_mod_eq : type_of% @_root_.Int.trailingZeros_eq_zero_of_mod_eq := by
  intro i odd
  have ne : i ≠ 0 := by
    intro h
    subst i
    exact (by decide : (0 : Int) ≠ 1) odd
  rw [_root_.Int.trailingZeros, dite_eq_right ne]
  have base (k : Nat) (bound : i.natAbs ≤ k) : _root_.Int.trailingZeros.aux k i ne bound 0 = 0 := by
    cases k with
    | zero => exact False.elim (ne (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero bound)))
    | succ k =>
      rw [_root_.Int.trailingZeros.aux.eq_1 i ne 0 k (Nat.succ_ne_zero k)]
      exact dite_eq_right (fun even => (by decide : (0 : Int) ≠ 1) (even.symm.trans odd))
  exact base _ (Nat.le_refl _)

public theorem Int.trailingZeros_two_mul_add_one : type_of% @_root_.Int.trailingZeros_two_mul_add_one := by
  intro i
  apply Int.trailingZeros_eq_zero_of_mod_eq
  exact Int.mul_add_emod_self_left 2 i 1

public theorem Int.trailingZeros_two_mul : type_of% @_root_.Int.trailingZeros_two_mul := by
  intro i hi
  have nz : (2 : Int) ≠ 0 := by decide
  have twice : 2*i ≠ 0 := Int.mul_ne_zero nz hi
  have even : (2*i) % 2 = 0 := Int.mul_emod_right _ _
  have div : (2*i) / 2 = i := Int.mul_ediv_cancel_left i nz
  rw [_root_.Int.trailingZeros, dite_eq_right twice, _root_.Int.trailingZeros, dite_eq_right hi]
  have step (k : Nat) (hk : (2*i).natAbs ≤ k) :
      _root_.Int.trailingZeros.aux k (2*i) twice hk 0 =
      _root_.Int.trailingZeros.aux i.natAbs i hi (Nat.le_refl _) 0 + 1 := by
    cases k with
    | zero => exact False.elim (twice (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)))
    | succ k =>
      rw [_root_.Int.trailingZeros.aux.eq_1 (2*i) twice 0 k (Nat.succ_ne_zero k), dite_eq_left even]
      have normalize (j : Int) (eq : j = i) (hn : j ≠ 0) (hb : j.natAbs ≤ k) :
          _root_.Int.trailingZeros.aux k j hn hb 1 =
          _root_.Int.trailingZeros.aux i.natAbs i hi (Nat.le_refl _) 0 + 1 := by
        subst j
        exact (_root_.Int.trailingZeros_aux_succ (i := i) (k := k) (hi := hn) (hk := hb) (acc := 0)).trans
          (congrArg Nat.succ (_root_.Int.trailingZeros_aux_irrel hi hb (Nat.le_refl _)))
      exact normalize _ div _ _
  exact step _ (Nat.le_refl _)

public theorem Int.two_pow_trailingZeros_dvd : type_of% @_root_.Int.two_pow_trailingZeros_dvd := by
  intro a ha
  have factor (k : Nat) (i : Int) (hi : i ≠ 0) (hk : i.natAbs ≤ k) (acc : Nat)
      (split : a = 2^acc * i) : 2 ^ _root_.Int.trailingZeros.aux k i hi hk acc ∣ a := by
    induction k generalizing i acc with
    | zero => exact False.elim (hi (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)))
    | succ k ih =>
      rw [_root_.Int.trailingZeros.aux.eq_1 i hi acc k (Nat.succ_ne_zero k)]
      by_cases even : i % 2 = 0
      · rw [dite_eq_left even]
        apply ih
        rw [Int.pow_succ, Int.mul_assoc, Int.mul_ediv_cancel_of_emod_eq_zero even]
        exact split
      · rw [dite_eq_right even]
        exact ⟨i, split⟩
  rw [_root_.Int.trailingZeros, dite_eq_right ha]
  exact factor _ a ha (Nat.le_refl _) 0 (Int.one_mul a).symm

public theorem Int.natCast_eq_zero : type_of% @_root_.Int.natCast_eq_zero :=
  ⟨Int.ofNat.inj, congrArg Int.ofNat⟩

public theorem Dyadic.toRat_eq_zero_iff : type_of% @_root_.Dyadic.toRat_eq_zero_iff := by
  intro x
  constructor
  · intro eq
    cases x with
    | zero => rfl
    | ofOdd n k odd =>
      have nz : n ≠ 0 := by
        intro h
        subst n
        exact (by decide : (0 : Int) ≠ 1) odd
      cases k with
      | ofNat k => exact False.elim (nz (congrArg Rat.num eq))
      | negSucc k =>
        have mul : n * ((2 ^ (k+1) : Nat) : Int) = 0 := congrArg Rat.num eq
        exact False.elim (Int.mul_ne_zero nz
          (fun h => Nat.ne_of_gt (Nat.pow_pos Nat.zero_lt_two) (Int.ofNat.inj h)) mul)
  · intro eq
    rw [eq]
    rfl

public theorem Dyadic.ofOdd_eq_ofIntWithPrec : type_of% @_root_.Dyadic.ofOdd_eq_ofIntWithPrec := by
  intro n k hn
  have ne : n ≠ 0 := by
    intro h
    subst n
    exact (by decide : (0 : Int) ≠ 1) hn
  rw [_root_.Dyadic.ofIntWithPrec, dite_eq_right ne]
  have tz := Int.trailingZeros_eq_zero_of_mod_eq hn
  congr 1
  · rw [tz, Int.shiftRight_zero]
  · rw [tz]
    exact (Int.sub_zero k).symm

public theorem Rat.toDyadic_mkRat : type_of% @_root_.Rat.toDyadic_mkRat := by
  intro a b prec
  by_cases hb : b = 0
  · subst b
    rw [Rat.mkRat_zero, Nat.zero_shiftLeft]
    change _ = Dyadic.ofIntWithPrec ((a <<< prec.toNat) / (0 : Int)) prec
    rw [Int.ediv_zero]
    cases prec with
    | ofNat k =>
      change Dyadic.ofIntWithPrec ((0 <<< k : Int) / 1) _ = _
      rw [Nat.zero_shiftLeft]
      rfl
    | negSucc k =>
      change Dyadic.ofIntWithPrec ((0 : Int) / _) _ = _
      rw [Int.zero_ediv]
  · rcases h : mkRat a b with ⟨n, d, hnz, hr⟩
    obtain ⟨m, hm, rfl, rfl⟩ := Rat.mkRat_num_den hb h
    have mpos : (0 : Int) ≤ m := Int.natCast_nonneg _
    have mnz : (m : Int) ≠ 0 := fun e => hm (Int.ofNat.inj e)
    cases prec with
    | ofNat k =>
      simp only [_root_.Rat.toDyadic, Int.ofNat_eq_natCast, Int.toNat_natCast, Int.toNat_neg_natCast,
        Nat.shiftLeft_zero, Int.natCast_mul]
      rw [Int.mul_comm (d : Int), ← Int.ediv_ediv_of_nonneg mpos, ← Int.shiftLeft_mul, Int.mul_ediv_cancel _ mnz]
    | negSucc k =>
      simp only [_root_.Rat.toDyadic, Int.natCast_shiftLeft, Int.negSucc_eq, ← Int.natCast_add_one,
        Int.toNat_neg_natCast, Int.shiftLeft_zero, Int.neg_neg, Int.toNat_natCast, Int.natCast_mul]
      rw [Int.mul_comm (d : Int), ← Int.mul_shiftLeft, ← Int.ediv_ediv_of_nonneg mpos, Int.mul_ediv_cancel _ mnz]

public theorem Dyadic.toRat_inj : type_of% @_root_.Dyadic.toRat_inj := by
  intro x y
  constructor
  · intro eq
    let prec : Int := max (x.precision.getD 0) (y.precision.getD 0)
    have bound (v : Dyadic) (le : v.precision.getD 0 ≤ prec) : v.precision ≤ some prec := by
      cases v with
      | zero => trivial
      | ofOdd _ _ _ => exact le
    have first := _root_.Dyadic.roundDown_eq_self_of_le (bound x (Int.le_max_left _ _))
    have second := _root_.Dyadic.roundDown_eq_self_of_le (bound y (Int.le_max_right _ _))
    have rounded := congrArg (fun r : Rat => r.toDyadic prec) eq
    rw [_root_.Dyadic.toDyadic_toRat, _root_.Dyadic.toDyadic_toRat, first, second] at rounded
    exact rounded
  · exact congrArg _root_.Dyadic.toRat

private theorem shiftLeft_mul_zpow (num : Int) (d : Nat) (k e : Int) (aligned : (d : Int) + -k = -e) :
    ((num <<< d : Int) : Rat) * (2 : Rat) ^ (-k) = (num : Rat) * 2 ^ (-e) := by
  rw [_root_.Int.shiftLeft_eq, Rat.intCast_mul, Rat.intCast_pow, Rat.mul_assoc]
  change (num : Rat) * ((2 : Rat) ^ (d : Int) * 2 ^ (-k)) = _
  rw [← Rat.zpow_add (by decide : (2 : Rat) ≠ 0), aligned]

public theorem Dyadic.toRat_add : type_of% @_root_.Dyadic.toRat_add := by
  intro x y
  cases x with
  | zero => exact (Rat.zero_add _).symm
  | ofOdd a k ha =>
    cases y with
    | zero => exact (Rat.add_zero _).symm
    | ofOdd b e hb =>
      change (_root_.Dyadic.add _ _).toRat = _
      rw [_root_.Dyadic.add, _root_.Dyadic.toRat_ofOdd_eq_mul_two_pow, _root_.Dyadic.toRat_ofOdd_eq_mul_two_pow]
      split
      · rename_i eq
        have same := Int.sub_eq_zero.mp eq
        subst e
        rw [_root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_add, Rat.add_mul]
      · rename_i d eq
        rw [_root_.Dyadic.toRat_ofOdd_eq_mul_two_pow, Rat.intCast_add, Rat.add_mul]
        apply congrArg ((a : Rat) * 2 ^ (-k) + ·)
        apply shiftLeft_mul_zpow
        change Int.ofNat d.succ + -k = -e
        rw [← eq]
        omega
      · rename_i d eq
        rw [_root_.Dyadic.toRat_ofOdd_eq_mul_two_pow, Rat.intCast_add, Rat.add_mul]
        apply congrArg (· + (b : Rat) * 2 ^ (-e))
        apply shiftLeft_mul_zpow
        omega

public theorem Dyadic.blt_iff_toRat : type_of% @_root_.Dyadic.blt_iff_toRat := by
  intro x y
  have pos (k : Int) : (0 : Rat) < 2 ^ k := Rat.zpow_pos (by decide)
  have dec (a b : Int) : decide (a < b) = true ↔ a < b := ⟨of_decide_eq_true, decide_eq_true⟩
  cases x with
  | zero =>
    cases y with
    | zero => decide
    | ofOdd b e hb =>
      rw [_root_.Dyadic.toRat_ofOdd_eq_mul_two_pow]
      change decide (0 < b) = true ↔ (0 : Rat) < b * 2 ^ (-e)
      exact (dec 0 b).trans (_root_.Rat.intCast_pos.symm.trans (Rat.mul_pos_iff_of_pos_right (pos _)).symm)
  | ofOdd a k ha =>
    cases y with
    | zero =>
      rw [_root_.Dyadic.toRat_ofOdd_eq_mul_two_pow]
      change decide (a < 0) = true ↔ (a : Rat) * 2 ^ (-k) < 0
      exact (dec a 0).trans (_root_.Rat.intCast_neg_iff.symm.trans (Rat.mul_neg_iff_of_pos_right (pos _)).symm)
    | ofOdd b e hb =>
      rw [_root_.Dyadic.blt, _root_.Dyadic.toRat_ofOdd_eq_mul_two_pow, _root_.Dyadic.toRat_ofOdd_eq_mul_two_pow]
      split
      · rename_i d h
        have aligned : (d : Int) + -e = -k := by
          change Int.ofNat d + -e = -k
          rw [← h]
          omega
        rw [← shiftLeft_mul_zpow a d e k aligned]
        exact (dec _ _).trans (Rat.intCast_lt_intCast.symm.trans (Rat.mul_lt_mul_right (pos _)).symm)
      · rename_i d h
        have aligned : ((d+1 : Nat) : Int) + -k = -e := by omega
        rw [← shiftLeft_mul_zpow b (d+1) k e aligned]
        exact (dec _ _).trans (Rat.intCast_lt_intCast.symm.trans (Rat.mul_lt_mul_right (pos _)).symm)

public theorem Dyadic.ble_iff_toRat : type_of% @_root_.Dyadic.ble_iff_toRat := by
  intro x y
  exact (_root_.Dyadic.blt_eq_false_iff (x := y) (y := x)).symm.trans
    (Bool.eq_false_iff.trans ((not_congr (Dyadic.blt_iff_toRat (x := y) (y := x))).trans Rat.not_lt))

public theorem Dyadic.not_lt : type_of% @_root_.Dyadic.not_lt := by
  intro x y
  exact (not_congr (Dyadic.blt_iff_toRat (x := x) (y := y))).trans (Rat.not_lt.trans Dyadic.ble_iff_toRat.symm)

public theorem Dyadic.not_le : type_of% @_root_.Dyadic.not_le := by
  intro x y
  exact (not_congr (Dyadic.ble_iff_toRat (x := x) (y := y))).trans (Rat.not_le.trans Dyadic.blt_iff_toRat.symm)

public theorem Dyadic.instLawfulOrderLT : type_of% @_root_.Dyadic.instLawfulOrderLT where
  lt_iff a b := by
    constructor
    · intro lt
      have nle := Dyadic.not_le.mpr lt
      exact ⟨(_root_.Dyadic.le_total a b).resolve_right nle, nle⟩
    · exact fun h => Dyadic.not_le.mp h.2

public theorem Dyadic.neg_ofIntWithPrec : type_of% @_root_.Dyadic.neg_ofIntWithPrec := by
  intro i prec
  apply _root_.Dyadic.toRat_inj.mp
  rw [_root_.Dyadic.toRat_neg, _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
    _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_neg, Rat.neg_mul]

public theorem Rat.floor_le : type_of% @_root_.Rat.floor_le := by
  intro x
  apply (Rat.le_iff _ _).mpr
  change x.floor * (x.den : Int) ≤ x.num * 1
  rw [_root_.Rat.floor_def, Int.mul_one]
  exact Int.ediv_mul_le _ (fun h => x.den_nz (Int.ofNat.inj h))

public theorem Rat.toRat_toDyadic : type_of% @_root_.Rat.toRat_toDyadic := by
  intro x p
  have floor_mk (n : Int) (d : Nat) (hd : d ≠ 0) : (mkRat n d).floor = n / (d : Int) := by
    rcases h : mkRat n d with ⟨u,v,hv,r⟩
    obtain ⟨m,hm,hn,he⟩ := _root_.Rat.mkRat_num_den hd h
    rw [_root_.Rat.floor_def, hn, he, Int.natCast_mul]
    exact (Int.mul_ediv_mul_of_pos_left _ _ (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hm))).symm
  have ratpow (k : Nat) : (2 : Rat)^k = mkRat (2^k : Int) 1 :=
    (_root_.Rat.intCast_pow 2 k).symm.trans (_root_.Rat.mkRat_one _).symm
  rw [_root_.Rat.toDyadic_eq_ofIntWithPrec, _root_.Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow,
    _root_.Rat.zpow_neg, _root_.Rat.div_def]
  apply congrArg (fun n : Int => (n : Rat) * ((2 : Rat)^p)⁻¹)
  have rep := _root_.Rat.mkRat_self x
  cases p with
  | ofNat p =>
    change (x.num <<< p) / ((x.den <<< (-(Int.ofNat p)).toNat : Nat) : Int) = (x * (2 : Rat)^p).floor
    have neg : (-(Int.ofNat p)).toNat = 0 := Int.toNat_neg_natCast p
    rw [neg, Nat.shiftLeft_zero, _root_.Int.shiftLeft_eq, ratpow]
    have prod := (congrArg (· * mkRat (2^p : Int) 1) rep).symm.trans
      (_root_.Rat.mkRat_mul_mkRat x.num (2^p : Int) x.den 1)
    rw [prod, Nat.mul_one, floor_mk _ _ x.den_nz]
  | negSucc p =>
    have positive : (2^(p+1) : Nat) ≠ 0 := Nat.ne_of_gt (Nat.pow_pos Nat.zero_lt_two)
    have inv : ((2 : Rat)^(p+1))⁻¹ = mkRat 1 (2^(p+1)) := by
      rw [ratpow]
      change (Rat.divInt (2^(p+1):Int) 1)⁻¹ = Rat.divInt 1 (Int.ofNat (2^(p+1)))
      exact _root_.Rat.inv_divInt _ _
    change (x.num <<< 0) / ((x.den <<< (p+1) : Nat) : Int) = (x * ((2 : Rat)^(p+1))⁻¹).floor
    rw [Int.shiftLeft_zero, Nat.shiftLeft_eq, inv]
    have prod := (congrArg (· * mkRat 1 (2^(p+1))) rep).symm.trans
      (_root_.Rat.mkRat_mul_mkRat x.num 1 x.den (2^(p+1)))
    rw [prod, Int.mul_one, floor_mk _ _ (Nat.mul_ne_zero x.den_nz positive)]

public theorem Int.beq'_eq_beq : type_of% @_root_.Int.beq'_eq_beq := by
  intro a b
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply beq_iff_eq.mpr
    cases a <;> cases b
    · exact congrArg _root_.Int.ofNat (Nat.eq_of_beq_eq_true h)
    · exact nomatch h
    · exact nomatch h
    · exact congrArg _root_.Int.negSucc (Nat.eq_of_beq_eq_true h)
  · intro h
    cases eq_of_beq h
    cases a <;> exact Nat.beq_refl _

private theorem trueIntBEq {a b : Int} (h : Int.beq' a b = true) : a = b :=
  eq_of_beq ((Int.beq'_eq_beq ..).symm.trans h)

public theorem Int.Internal.Linear.Poly.denote'_go_eq_denote :
    type_of% @_root_.Int.Internal.Linear.Poly.denote'_go_eq_denote := by
  intro ctx p
  induction p with
  | num k =>
    intro r
    change (Bool.rec (r + k) r (Int.beq' k 0)) = k + r
    cases h : Int.beq' k 0 with
    | false => exact Int.add_comm ..
    | true => cases trueIntBEq h; exact (Int.zero_add r).symm
  | add k v p ih =>
    intro r
    change Bool.rec _ _ (Int.beq' k 1) = k * v.denote ctx + p.denote ctx + r
    have reorder (a b c : Int) : a + (c + b) = (b + a) + c :=
      (congrArg (a + ·) (Int.add_comm c b)).trans ((Int.add_assoc ..).symm.trans (congrArg (· + c) (Int.add_comm a b)))
    cases h : Int.beq' k 1 with
    | false => exact (ih _).trans (reorder ..)
    | true =>
      cases trueIntBEq h
      rw [Int.one_mul]
      exact (ih _).trans (reorder ..)

public theorem Int.Internal.Linear.Poly.denote'_eq_denote :
    type_of% @_root_.Int.Internal.Linear.Poly.denote'_eq_denote := by
  intro ctx p
  cases p with
  | num k => rfl
  | add k v p =>
    change Bool.rec _ _ (Int.beq' k 1) = k * v.denote ctx + p.denote ctx
    cases h : Int.beq' k 1 with
    | false => exact (Int.Internal.Linear.Poly.denote'_go_eq_denote ..).trans (Int.add_comm ..)
    | true =>
      cases trueIntBEq h
      rw [Int.one_mul]
      exact (Int.Internal.Linear.Poly.denote'_go_eq_denote ..).trans (Int.add_comm ..)

open _root_.Int.Internal.Linear in
public theorem Int.Internal.Linear.Poly.mul_k_eq_mul : type_of% @_root_.Int.Internal.Linear.Poly.mul_k_eq_mul := by
  intro k p
  unfold Poly.mul_k Poly.mul
  rw [← _root_.Int.beq'_eq_beq]
  cases _root_.Int.beq' k 0 with
  | true => rfl
  | false =>
    induction p with
    | num => rfl
    | add c x t ih => exact congrArg (Poly.add (k*c) x) ih

open _root_.Int.Internal.Linear in
private theorem combineScaled {ctx : Context} (fuel : Nat) (a b : Int) (p q : Poly) :
    (Poly.combine_mul_k' fuel a b p q).denote ctx = a * p.denote ctx + b * q.denote ctx := by
  induction fuel generalizing p q with
  | zero =>
    change ((p.mul a).append (q.mul b)).denote ctx = _
    rw [Poly.denote_append, Poly.denote_mul, Poly.denote_mul]
  | succ fuel ih =>
    cases p <;> cases q
    · rfl
    · rename_i c l y q
      change (b*l) * y.denote ctx + (Poly.combine_mul_k' fuel a b (.num c) q).denote ctx = a*c + b * (l * y.denote ctx + q.denote ctx)
      simp only [ih, Poly.denote, Int.mul_add, Int.mul_assoc]
      ac_rfl
    · rename_i k x p l
      change (a*k) * x.denote ctx + (Poly.combine_mul_k' fuel a b p (.num l)).denote ctx = a * (k * x.denote ctx + p.denote ctx) + b*l
      simp only [ih, Poly.denote, Int.mul_add, Int.mul_assoc]
      ac_rfl
    · rename_i k x p l y q
      change Poly.denote ctx (Bool.rec _ _ (x.beq y)) = _
      cases same : x.beq y with
      | false =>
        change Poly.denote ctx (Bool.rec _ _ (y.blt x)) = _
        cases y.blt x with
        | false =>
          change (b*l) * y.denote ctx + (Poly.combine_mul_k' fuel a b (.add k x p) q).denote ctx = _
          simp only [ih, Poly.denote, Int.mul_add, Int.mul_assoc]
          ac_rfl
        | true =>
          change (a*k) * x.denote ctx + (Poly.combine_mul_k' fuel a b p (.add l y q)).denote ctx = _
          simp only [ih, Poly.denote, Int.mul_add, Int.mul_assoc]
          ac_rfl
      | true =>
        cases Nat.eq_of_beq_eq_true same
        change Poly.denote ctx (Bool.rec _ _ (Int.beq' (a*k+b*l) 0)) = _
        cases zero : Int.beq' (a*k+b*l) 0 with
        | false =>
          change (a*k+b*l) * x.denote ctx + (Poly.combine_mul_k' fuel a b p q).denote ctx = _
          simp only [ih, Poly.denote, Int.mul_add, Int.add_mul, Int.mul_assoc]
          ac_rfl
        | true =>
          have hz : a*k+b*l = 0 := eq_of_beq ((_root_.Int.beq'_eq_beq ..).symm.trans zero)
          change (Poly.combine_mul_k' fuel a b p q).denote ctx = _
          rw [ih]
          change _ = a * (k * x.denote ctx + p.denote ctx) + b * (l * x.denote ctx + q.denote ctx)
          rw [Int.mul_add, Int.mul_add, ←Int.mul_assoc, ←Int.mul_assoc]
          calc
            _ = (a*k+b*l) * x.denote ctx + (a * p.denote ctx + b * q.denote ctx) := by
              rw [hz, Int.zero_mul, Int.zero_add]
            _ = _ := by rw [Int.add_mul]; ac_rfl

open _root_.Int.Internal.Linear in
public theorem Int.Internal.Linear.Poly.denote_combine_mul_k : type_of% @_root_.Int.Internal.Linear.Poly.denote_combine_mul_k := by
  intro ctx a b p q
  unfold Poly.combine_mul_k
  cases za : Int.beq' a 0 with
  | true =>
    cases eq_of_beq ((_root_.Int.beq'_eq_beq ..).symm.trans za)
    rw [Int.zero_mul, Int.zero_add]
    exact (congrArg (Poly.denote ctx) (Int.Internal.Linear.Poly.mul_k_eq_mul ..)).trans (Poly.denote_mul ..)
  | false =>
    cases zb : Int.beq' b 0 with
    | true =>
      cases eq_of_beq ((_root_.Int.beq'_eq_beq ..).symm.trans zb)
      rw [Int.zero_mul, Int.add_zero]
      exact (congrArg (Poly.denote ctx) (Int.Internal.Linear.Poly.mul_k_eq_mul ..)).trans (Poly.denote_mul ..)
    | false => exact combineScaled ..

public theorem Int.ofNat_add_negSucc_of_lt : type_of% @_root_.Int.ofNat_add_negSucc_of_lt := by
  intro m n h
  change (m : Int) + -((n : Int)+1) = -(((n-m : Nat) : Int)+1)
  rw [Int.ofNat_sub (Nat.le_of_lt_succ h)]
  omega

public theorem Int.cooper_resolution_dvd_right : type_of% @_root_.Int.cooper_resolution_dvd_right := by
  intro a b c d s p q ha hb hd
  have left := _root_.Int.cooper_resolution_dvd_left (a := b) (b := a) (c := -c) (p := -q) (q := -p) (s := s) hb ha hd
  constructor
  · rintro ⟨x, lower, upper, divides⟩
    have witness : ∃ y, -q ≤ b*y ∧ a*y ≤ -p ∧ d ∣ -c*y+s := by
      refine ⟨-x, ?_, ?_, ?_⟩
      · rw [Int.mul_neg]; exact Int.neg_le_neg upper
      · rw [Int.mul_neg]; exact Int.neg_le_neg lower
      · rw [Int.neg_mul_neg]; exact divides
    obtain ⟨k, nonneg, bound, interval, divisor, residue⟩ := left.mp witness
    rw [Int.gcd_neg] at bound
    rw [Int.mul_neg, Int.mul_neg] at interval
    rw [Int.neg_mul_neg] at residue
    exact ⟨k, nonneg, bound, by omega, divisor, residue⟩
  · rintro ⟨k, nonneg, bound, interval, divisor, residue⟩
    rw [← @Int.gcd_neg (b*d) c] at bound
    have reflected : a*k+a*(-q) ≤ b*(-p) := by rw [Int.mul_neg, Int.mul_neg]; omega
    have reflectedResidue : b*d ∣ -c*k+(-c)*(-q)+b*s := by rw [Int.neg_mul_neg]; exact residue
    obtain ⟨y, lo, hi, divides⟩ := left.mpr ⟨k, nonneg, bound, reflected, divisor, reflectedResidue⟩
    refine ⟨-y, ?_, ?_, ?_⟩
    · rw [Int.mul_neg]; omega
    · rw [Int.mul_neg]; omega
    · rw [Int.mul_neg, ← Int.neg_mul]; exact divides

end OmegaChecks.InitPort.Alternatives
