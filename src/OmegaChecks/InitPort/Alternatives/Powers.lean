module
import all Init.Data.Rat.Basic
import all Init.Data.Rat.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.gcd_mul_right_right_of_gcd_eq_one : type_of% @_root_.Nat.gcd_mul_right_right_of_gcd_eq_one := by
  intro n m k coprime
  apply Nat.dvd_antisymm
  · have divides := Nat.gcd_mul_right_dvd_mul_gcd n m k
    rw [coprime, Nat.one_mul] at divides
    exact divides
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left n k) (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right n k) m)

public theorem Nat.pow_lt_pow_left : type_of% @_root_.Nat.pow_lt_pow_left := by
  intro a b n lt nonzero
  cases n with
  | zero => exact False.elim (nonzero rfl)
  | succ n =>
    induction n with
    | zero =>
      change a ^ 1 < b ^ 1
      rw [Nat.pow_one, Nat.pow_one]
      exact lt
    | succ n ih =>
      rw [Nat.pow_succ a, Nat.pow_succ b]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt lt))
        (Nat.mul_lt_mul_of_pos_right (ih (Nat.succ_ne_zero _)) (Nat.lt_of_le_of_lt (Nat.zero_le _) lt))

public theorem Rat.pow._proof_1 : type_of% @_root_.Rat.pow._proof_1 :=
  fun q _ => Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero q.den_nz))

public theorem Rat.pow_def._proof_1 : type_of% @_root_.Rat.pow_def._proof_1 :=
  Rat.pow._proof_1

public theorem Rat.divInt_eq_divInt_iff : type_of% @_root_.Rat.divInt_eq_divInt_iff := by
  intro d₁ d₂ n₁ n₂ z₁ z₂
  have transpose (a b : Int) : a = -b ↔ -a = b :=
    ⟨fun h => (congrArg Neg.neg h).trans (Int.neg_neg b),
     fun h => (Int.neg_neg a).symm.trans (congrArg Neg.neg h)⟩
  cases d₁ with
  | ofNat d₁ =>
    cases d₂ with
    | ofNat d₂ =>
      exact Rat.mkRat_eq_iff (fun h => z₁ (congrArg Int.ofNat h)) (fun h => z₂ (congrArg Int.ofNat h))
    | negSucc d₂ =>
      change Rat.divInt n₁ (Int.ofNat d₁) = Rat.divInt n₂ (-(Int.ofNat (d₂+1))) ↔ _
      rw [Rat.divInt_neg']
      change mkRat n₁ d₁ = mkRat (-n₂) (d₂+1) ↔ _
      apply (Rat.mkRat_eq_iff (fun h => z₁ (congrArg Int.ofNat h)) (Nat.succ_ne_zero _)).trans
      rw [Int.neg_mul]
      change _ ↔ n₁ * (-(Int.ofNat (d₂+1))) = n₂ * Int.ofNat d₁
      rw [Int.mul_neg]
      exact transpose _ _
  | negSucc d₁ =>
    cases d₂ with
    | ofNat d₂ =>
      change Rat.divInt n₁ (-(Int.ofNat (d₁+1))) = Rat.divInt n₂ (Int.ofNat d₂) ↔ _
      rw [Rat.divInt_neg']
      change mkRat (-n₁) (d₁+1) = mkRat n₂ d₂ ↔ _
      apply (Rat.mkRat_eq_iff (Nat.succ_ne_zero _) (fun h => z₂ (congrArg Int.ofNat h))).trans
      rw [Int.neg_mul]
      change _ ↔ n₁ * Int.ofNat d₂ = n₂ * (-(Int.ofNat (d₁+1)))
      rw [Int.mul_neg]
      exact (transpose _ _).symm
    | negSucc d₂ =>
      change Rat.divInt n₁ (-(Int.ofNat (d₁+1))) = Rat.divInt n₂ (-(Int.ofNat (d₂+1))) ↔ _
      rw [Rat.divInt_neg', Rat.divInt_neg']
      change mkRat (-n₁) (d₁+1) = mkRat (-n₂) (d₂+1) ↔ _
      apply (Rat.mkRat_eq_iff (Nat.succ_ne_zero _) (Nat.succ_ne_zero _)).trans
      rw [Int.neg_mul, Int.neg_mul]
      change _ ↔ n₁ * (-(Int.ofNat (d₂+1))) = n₂ * (-(Int.ofNat (d₁+1)))
      rw [Int.mul_neg, Int.mul_neg]
      rfl

public theorem Rat.divInt_self' : type_of% @_root_.Rat.divInt_self' := by
  intro n hn
  change Rat.divInt n n = Rat.divInt 1 1
  apply (Rat.divInt_eq_divInt_iff hn (by decide)).mpr
  rw [Int.mul_one, Int.one_mul]

public theorem Rat.mul_inv_cancel : type_of% @_root_.Rat.mul_inv_cancel := by
  intro a ha
  have numerator : a.num ≠ 0 := fun h => ha (Rat.num_eq_zero.mp h)
  have denominator : (a.den : Int) ≠ 0 := fun h => a.den_nz (Int.ofNat.inj h)
  calc
    a * a⁻¹ = Rat.divInt a.num a.den * a⁻¹ := congrArg (· * a⁻¹) (Rat.num_divInt_den a).symm
    _ = Rat.divInt (a.num * (a.den : Int)) ((a.den : Int) * a.num) := by
      rw [Rat.inv_def, Rat.divInt_mul_divInt]
    _ = 1 := by
      rw [Int.mul_comm a.num]
      exact Rat.divInt_self' (Int.mul_ne_zero denominator numerator)

public theorem Rat.inv_inv : type_of% @_root_.Rat.inv_inv := by
  intro a
  by_cases zero : a = 0
  · subst a
    rw [Rat.inv_zero, Rat.inv_zero]
  · exact Rat.inv_eq_of_mul_eq_one (Rat.inv_mul_cancel a zero)

public theorem Rat.zpow_add_one : type_of% @_root_.Rat.zpow_add_one := by
  intro q hq m
  cases m with
  | ofNat n => exact Rat.pow_succ q n
  | negSucc n =>
    cases n with
    | zero =>
      change q ^ (0 : Nat) = (q ^ (1 : Nat))⁻¹ * q
      rw [Rat.pow_zero, Rat.pow_one, Rat.inv_mul_cancel q hq]
    | succ n =>
      change (q ^ (n+1))⁻¹ = (q ^ ((n+1)+1))⁻¹ * q
      rw [Rat.pow_succ q (n+1), Rat.inv_mul_rev, Rat.mul_comm q⁻¹,
        Rat.mul_assoc, Rat.inv_mul_cancel q hq, Rat.mul_one]

public theorem Rat.divInt_num_den : type_of% @_root_.Rat.divInt_num_den := by
  intro d n n' d' nz c hd eq
  cases d with
  | ofNat d =>
    obtain ⟨k, hk, hn, hden⟩ := Rat.mkRat_num_den (fun h => hd (congrArg Int.ofNat h)) eq
    exact ⟨k, fun h => hk (Int.ofNat.inj h), hn, congrArg Int.ofNat hden⟩
  | negSucc d =>
    change Rat.divInt n (-(Int.ofNat (d+1))) = _ at eq
    rw [Rat.divInt_neg'] at eq
    obtain ⟨k, hk, hn, hden⟩ := Rat.mkRat_num_den (Nat.succ_ne_zero d) eq
    refine ⟨-(k : Int), fun h => hk (Int.ofNat.inj (Int.neg_eq_zero.mp h)), ?_, ?_⟩
    · rw [Int.mul_neg]
      exact (Int.neg_neg n).symm.trans (congrArg Neg.neg hn)
    · change -(Int.ofNat (d+1)) = (d' : Int) * (-(k : Int))
      rw [Int.mul_neg]
      exact congrArg Neg.neg (congrArg Int.ofNat hden)

public theorem Rat.divInt_mul_left : type_of% @_root_.Rat.divInt_mul_left := by
  intro n d a ha
  by_cases hz : d = 0
  · subst d
    rw [Int.mul_zero, Rat.divInt_zero, Rat.divInt_zero]
  · apply (Rat.divInt_eq_divInt_iff (Int.mul_ne_zero ha hz) hz).mpr
    rw [Int.mul_assoc, Int.mul_left_comm]

public theorem Rat.lt_iff : type_of% @_root_.Rat.lt_iff := by
  intro a b
  have ap : (0 : Int) < a.den := Int.natCast_pos.mpr (Nat.pos_of_ne_zero a.den_nz)
  have bp : (0 : Int) < b.den := Int.natCast_pos.mpr (Nat.pos_of_ne_zero b.den_nz)
  change _root_.Rat.blt a b = true ↔ _
  unfold _root_.Rat.blt
  by_cases ltge : (decide (a.num < 0) && decide (0 ≤ b.num)) = true
  · rw [ite_eq_left ltge]
    have signs := Bool.and_eq_true_iff.mp ltge
    exact ⟨fun _ => Int.lt_of_lt_of_le (Int.mul_neg_of_neg_of_pos (of_decide_eq_true signs.1) bp)
      (Int.mul_nonneg (of_decide_eq_true signs.2) (Int.le_of_lt ap)), fun _ => rfl⟩
  · rw [ite_eq_right ltge]
    by_cases az : a.num = 0
    · rw [ite_eq_left az, az, Int.zero_mul]
      constructor
      · intro lt
        exact Int.mul_pos (of_decide_eq_true lt) ap
      · intro lt
        apply decide_eq_true
        apply Int.lt_of_not_ge
        intro nonpos
        exact Int.not_le_of_gt lt (Int.mul_nonpos_of_nonpos_of_nonneg nonpos (Int.le_of_lt ap))
    · rw [ite_eq_right az]
      by_cases gtle : (decide (0 < a.num) && decide (b.num ≤ 0)) = true
      · rw [ite_eq_left gtle]
        have signs := Bool.and_eq_true_iff.mp gtle
        have reversed := Int.le_trans (Int.mul_nonpos_of_nonpos_of_nonneg (of_decide_eq_true signs.2) (Int.le_of_lt ap))
          (Int.le_of_lt (Int.mul_pos (of_decide_eq_true signs.1) bp))
        exact ⟨fun e => Bool.noConfusion e, fun lt => False.elim (Int.not_le_of_gt lt reversed)⟩
      · rw [ite_eq_right gtle]
        exact ⟨of_decide_eq_true, decide_eq_true⟩

public theorem Rat.not_lt : type_of% @_root_.Rat.not_lt := by
  intro a b
  change (¬ a.blt b = true) ↔ a.blt b = false
  cases a.blt b with
  | false => exact ⟨fun _ => rfl, fun _ => Bool.false_ne_true⟩
  | true => exact ⟨fun h => False.elim (h rfl), fun e => Bool.noConfusion e⟩

public theorem Rat.not_le : type_of% @_root_.Rat.not_le := by
  intro a b
  change (¬ b.blt a = false) ↔ b.blt a = true
  cases b.blt a with
  | false => exact ⟨fun h => False.elim (h rfl), fun e => Bool.noConfusion e⟩
  | true => exact ⟨fun _ => rfl, fun _ h => Bool.noConfusion h⟩

public theorem Rat.le_iff : type_of% @_root_.Rat.le_iff := by
  intro a b
  exact Rat.not_lt.symm.trans ((not_congr (Rat.lt_iff b a)).trans Int.not_lt)

public theorem Rat.intCast_lt_intCast : type_of% @_root_.Rat.intCast_lt_intCast := by
  intro a b
  apply (Rat.lt_iff _ _).trans
  change a * 1 < b * 1 ↔ a < b
  rw [Int.mul_one, Int.mul_one]

public theorem Rat.intCast_le_intCast : type_of% @_root_.Rat.intCast_le_intCast := by
  intro a b
  apply (Rat.le_iff _ _).trans
  change a * 1 ≤ b * 1 ↔ a ≤ b
  rw [Int.mul_one, Int.mul_one]

public theorem Rat.add_assoc : type_of% @_root_.Rat.add_assoc := by
  intro a b c
  refine _root_.Rat.numDenCasesOn' a fun n d hd => ?_
  refine _root_.Rat.numDenCasesOn' b fun m e he => ?_
  refine _root_.Rat.numDenCasesOn' c fun k f hf => ?_
  change (mkRat n d + mkRat m e) + mkRat k f = mkRat n d + (mkRat m e + mkRat k f)
  rw [Rat.mkRat_add_mkRat _ _ hd he, Rat.mkRat_add_mkRat _ _ he hf,
    Rat.mkRat_add_mkRat _ _ (Nat.mul_ne_zero hd he) hf, Rat.mkRat_add_mkRat _ _ hd (Nat.mul_ne_zero he hf)]
  rw [Nat.mul_assoc]
  apply congrArg (fun v => mkRat v (d*(e*f)))
  conv => lhs; simp only [Int.add_mul, Int.mul_add, Int.natCast_mul, Int.mul_assoc, Int.add_assoc, Int.mul_comm, Int.mul_left_comm]
  conv => rhs; simp only [Int.add_mul, Int.mul_add, Int.natCast_mul, Int.mul_assoc, Int.add_assoc, Int.mul_comm, Int.mul_left_comm]

public theorem Rat.add_mul : type_of% @_root_.Rat.add_mul := by
  intro a b c
  refine _root_.Rat.numDenCasesOn' a fun n d hd => ?_
  refine _root_.Rat.numDenCasesOn' b fun m e he => ?_
  refine _root_.Rat.numDenCasesOn' c fun k f hf => ?_
  change (mkRat n d + mkRat m e) * mkRat k f = mkRat n d * mkRat k f + mkRat m e * mkRat k f
  rw [Rat.mkRat_add_mkRat _ _ hd he, Rat.mkRat_mul_mkRat, Rat.mkRat_mul_mkRat, Rat.mkRat_mul_mkRat,
    Rat.mkRat_add_mkRat _ _ (Nat.mul_ne_zero hd hf) (Nat.mul_ne_zero he hf)]
  rw [← Rat.mkRat_mul_right (n := (n * (e : Int) + m * (d : Int)) * k) (d := d * e * f) hf]
  congr 1
  · conv => lhs; simp only [Int.add_mul, Int.mul_add, Int.natCast_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    conv => rhs; simp only [Int.add_mul, Int.mul_add, Int.natCast_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  · conv => lhs; simp only [Nat.mul_comm, Nat.mul_left_comm]
    conv => rhs; simp only [Nat.mul_comm, Nat.mul_left_comm]

public theorem Rat.le_total : type_of% @_root_.Rat.le_total := by
  intro a b
  exact (Int.le_total (a.num * b.den) (b.num * a.den)).elim
    (fun h => Or.inl ((Rat.le_iff _ _).mpr h)) (fun h => Or.inr ((Rat.le_iff _ _).mpr h))

public theorem Rat.le_refl : type_of% @_root_.Rat.le_refl :=
  fun {a} => (Rat.le_iff a a).mpr (Int.le_refl _)

public theorem Rat.le_antisymm : type_of% @_root_.Rat.le_antisymm := by
  intro a b hab hba
  have cross := Int.le_antisymm ((Rat.le_iff _ _).mp hab) ((Rat.le_iff _ _).mp hba)
  have fractions := (Rat.divInt_eq_divInt_iff (fun h => a.den_nz (Int.ofNat.inj h))
    (fun h => b.den_nz (Int.ofNat.inj h))).mpr cross
  exact (Rat.num_divInt_den a).symm.trans (fractions.trans (Rat.num_divInt_den b))

public theorem Rat.le_trans : type_of% @_root_.Rat.le_trans := by
  intro a b c hab hbc
  apply (Rat.le_iff _ _).mpr
  apply Int.le_of_not_gt
  intro wrong
  have h₁ := Int.mul_le_mul_of_nonneg_right ((Rat.le_iff _ _).mp hab) (Int.natCast_nonneg c.den)
  have h₂ := Int.mul_le_mul_of_nonneg_right ((Rat.le_iff _ _).mp hbc) (Int.natCast_nonneg a.den)
  have h₃ := Int.mul_lt_mul_of_pos_right wrong (Int.natCast_pos.mpr (Nat.pos_of_ne_zero b.den_nz))
  rw [Int.mul_right_comm b.num] at h₂
  rw [Int.mul_right_comm c.num] at h₂
  rw [Int.mul_right_comm a.num] at h₁
  exact Int.not_le_of_gt h₃ (Int.le_trans h₁ h₂)

public theorem Rat.num_nonneg : type_of% @_root_.Rat.num_nonneg := by
  intro q
  apply Iff.symm
  apply (Rat.le_iff _ _).trans
  change (0 : Int) * q.den ≤ q.num * 1 ↔ 0 ≤ q.num
  rw [Int.zero_mul, Int.mul_one]

public theorem Rat.divInt_nonneg_iff_of_pos_right : type_of% @_root_.Rat.divInt_nonneg_iff_of_pos_right := by
  intro a b hb
  let q := Rat.divInt a b
  have eq : Rat.divInt a b = q := rfl
  obtain ⟨m, hm, hn, hd⟩ := _root_.Rat.divInt_num_den (Int.ne_of_gt hb) eq
  have positive : 0 < m := by
    apply Int.lt_of_not_ge
    intro nonpos
    exact (Int.not_le_of_gt hb) (hd ▸ Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) nonpos)
  apply Rat.num_nonneg.symm.trans
  change 0 ≤ q.num ↔ 0 ≤ a
  rw [hn]
  constructor
  · exact fun h => Int.mul_nonneg h (Int.le_of_lt positive)
  · intro h
    apply Int.le_of_not_gt
    exact fun neg => (Int.not_le_of_gt (Int.mul_neg_of_neg_of_pos neg positive)) h

public theorem Rat.mul_nonneg : type_of% @_root_.Rat.mul_nonneg := by
  intro a b
  refine _root_.Rat.numDenCasesOn' a fun n d hd => ?_
  refine _root_.Rat.numDenCasesOn' b fun m e he => ?_
  intro hn hm
  have dp : (0 : Int) < d := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd)
  have ep : (0 : Int) < e := Int.natCast_pos.mpr (Nat.pos_of_ne_zero he)
  rw [Rat.divInt_mul_divInt]
  exact (Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos dp ep)).mpr (Int.mul_nonneg
    ((Rat.divInt_nonneg_iff_of_pos_right dp).mp hn) ((Rat.divInt_nonneg_iff_of_pos_right ep).mp hm))

public theorem Rat.mul_pos : type_of% @_root_.Rat.mul_pos := by
  intro a b ha hb
  apply _root_.Rat.lt_of_le_of_ne (Rat.mul_nonneg (_root_.Rat.le_of_lt ha) (_root_.Rat.le_of_lt hb))
  intro e
  exact (_root_.Rat.mul_eq_zero.mp e.symm).elim (_root_.Rat.ne_of_gt ha) (_root_.Rat.ne_of_gt hb)

public theorem Rat.pow_pos : type_of% @_root_.Rat.pow_pos := by
  intro a n ha
  induction n with
  | zero => rw [Rat.pow_zero]; decide
  | succ n ih => rw [Rat.pow_succ]; exact Rat.mul_pos ih ha

public theorem Rat.inv_pos : type_of% @_root_.Rat.inv_pos := by
  intro a
  have positive (q : Rat) (hq : 0 < q) : 0 < q⁻¹ := by
    have hnq := _root_.Rat.ne_of_gt hq
    have npos : 0 < q.num := Int.lt_iff_le_and_ne.mpr
      ⟨Rat.num_nonneg.mpr (_root_.Rat.le_of_lt hq), fun eq => hnq (_root_.Rat.num_eq_zero.mp eq.symm)⟩
    have invNonneg : 0 ≤ q⁻¹ := by
      rw [_root_.Rat.inv_def]
      exact (Rat.divInt_nonneg_iff_of_pos_right npos).mpr (Int.natCast_nonneg _)
    apply _root_.Rat.lt_of_le_of_ne invNonneg
    intro eq
    have inverse := _root_.Rat.mul_inv_cancel q hnq
    rw [← eq, _root_.Rat.mul_zero] at inverse
    exact (by decide : (0 : Rat) ≠ 1) inverse
  exact ⟨fun h => _root_.Rat.inv_inv a ▸ positive a⁻¹ h, positive a⟩

public theorem Rat.zpow_pos : type_of% @_root_.Rat.zpow_pos := by
  intro a n ha
  cases n with
  | ofNat n => exact Rat.pow_pos ha
  | negSucc n => exact Rat.inv_pos.mpr (Rat.pow_pos ha)

public theorem Rat.mul_lt_mul_of_pos_right : type_of% @_root_.Rat.mul_lt_mul_of_pos_right := by
  intro a b c lt pos
  apply _root_.Rat.lt_of_le_of_ne (_root_.Rat.mul_le_mul_of_nonneg_right (_root_.Rat.le_of_lt lt) (_root_.Rat.le_of_lt pos))
  intro e
  have cancel := congrArg (· * c⁻¹) e
  change (a*c)*c⁻¹ = (b*c)*c⁻¹ at cancel
  rw [_root_.Rat.mul_assoc, _root_.Rat.mul_assoc, _root_.Rat.mul_inv_cancel c (_root_.Rat.ne_of_gt pos),
    _root_.Rat.mul_one, _root_.Rat.mul_one] at cancel
  exact _root_.Rat.ne_of_lt lt cancel

public theorem Rat.mul_lt_mul_right : type_of% @_root_.Rat.mul_lt_mul_right := by
  intro a b c pos
  constructor
  · intro lt
    apply _root_.Rat.not_le.mp
    intro reversed
    exact _root_.Rat.not_le.mpr lt (_root_.Rat.mul_le_mul_of_nonneg_right reversed (_root_.Rat.le_of_lt pos))
  · exact fun lt => Rat.mul_lt_mul_of_pos_right lt pos

public theorem Rat.mul_pos_iff_of_pos_right : type_of% @_root_.Rat.mul_pos_iff_of_pos_right := by
  intro a b pos
  have h := Rat.mul_lt_mul_right (a := 0) (b := a) pos
  rw [_root_.Rat.zero_mul] at h
  exact h

public theorem Rat.mul_neg_iff_of_pos_right : type_of% @_root_.Rat.mul_neg_iff_of_pos_right := by
  intro a b pos
  have h := Rat.mul_lt_mul_right (a := a) (b := 0) pos
  rw [_root_.Rat.zero_mul] at h
  exact h

public theorem Rat.le_of_mul_le_mul_right : type_of% @_root_.Rat.le_of_mul_le_mul_right := by
  intro a b c product pos
  exact Rat.not_lt.mp fun lt => Rat.not_lt.mpr product (Rat.mul_lt_mul_of_pos_right lt pos)

public theorem Rat.lt_of_mul_lt_mul_right : type_of% @_root_.Rat.lt_of_mul_lt_mul_right := by
  intro a b c product nonneg
  exact Rat.not_le.mp fun le => Rat.not_le.mpr product (_root_.Rat.mul_le_mul_of_nonneg_right le nonneg)

end OmegaChecks.InitPort.Alternatives
