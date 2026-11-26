module
public import Init.Data.Range.Polymorphic.Nat

/-! Direct witnesses for finite natural ranges and their successor law. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.PRange.instIsAlwaysFiniteNat : Rxc.IsAlwaysFinite Nat :=
  ⟨fun lo hi => ⟨hi.succ, Nat.not_le_of_gt
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self hi) (Nat.le_add_left hi.succ lo))⟩⟩

public theorem Std.PRange.instIsAlwaysFiniteNat_1 : Rxo.IsAlwaysFinite Nat :=
  ⟨fun lo hi => ⟨hi, Nat.not_lt_of_ge (Nat.le_add_left hi lo)⟩⟩

public theorem Std.PRange.instLawfulUpwardEnumerableNat : LawfulUpwardEnumerable Nat where
  ne_of_lt _ _ h := h.elim fun n eqSucc =>
    Nat.ne_of_lt ((Option.some.inj eqSucc) ▸ Nat.lt_add_of_pos_right (Nat.zero_lt_succ n))
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl

public theorem Std.PRange.instLawfulUpwardEnumerableLENat : LawfulUpwardEnumerableLE Nat where
  le_iff a b := ⟨fun h => ⟨b - a, congrArg some (Nat.add_sub_cancel' h)⟩,
    fun h => h.elim fun n eqSum => (Option.some.inj eqSum) ▸ Nat.le_add_right a n⟩

public theorem Std.PRange.instLawfulHasSizeNat : Rxc.LawfulHasSize Nat where
  size_eq_zero_of_not_le lo hi h := Nat.sub_eq_zero_of_le (Nat.lt_of_not_ge h)
  size_eq_one_of_succ?_eq_none lo _ _ h := False.elim (Option.noConfusion rfl (heq_of_eq (show some (lo + 1) = none from h)))
  size_eq_succ_of_succ?_eq_some lo hi lo' h eqNext := by
    have eq : lo + 1 = lo' := Option.some.inj eqNext
    subst lo'
    exact (Nat.succ_sub h).trans (congrArg Nat.succ (Nat.succ_sub_succ hi lo).symm)

private theorem openSize (lo hi : Nat) : Rxo.HasSize.size lo hi = hi - lo := by
  change (hi + 1 - lo) - 1 = hi - lo
  exact (Nat.sub_sub (hi + 1) lo 1).trans (Nat.succ_sub_succ hi lo)

public theorem Std.PRange.instLawfulHasSizeNat_1 : Rxo.LawfulHasSize Nat where
  size_eq_zero_of_not_le lo hi h := (openSize lo hi).trans (Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h))
  size_eq_one_of_succ?_eq_none lo _ _ h :=
    False.elim (Option.noConfusion rfl (heq_of_eq (show some (lo + 1) = none from h)))
  size_eq_succ_of_succ?_eq_some lo hi lo' h eqNext := by
    have eq : lo + 1 = lo' := Option.some.inj eqNext
    subst lo'
    rw [openSize, openSize, Nat.sub_succ]
    exact (Nat.succ_pred_eq_of_ne_zero (Nat.sub_ne_zero_of_lt h)).symm

end OmegaChecks.InitPort.Alternatives
