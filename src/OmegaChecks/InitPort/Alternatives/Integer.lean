module
public import Init.Data.Int.DivMod.Lemmas

namespace OmegaChecks.InitPort.Alternatives

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

end OmegaChecks.InitPort.Alternatives
