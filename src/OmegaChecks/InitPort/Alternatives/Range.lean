module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int

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

public theorem Std.PRange.instLawfulUpwardEnumerableInt : LawfulUpwardEnumerable Int where
  ne_of_lt a _ h := h.elim fun n eqNext =>
    have advance : a < a + (↑(n + 1) : Int) := Int.lt_add_of_pos_right a (Int.natCast_pos.mpr (Nat.zero_lt_succ n))
    Int.ne_of_lt ((Option.some.inj eqNext) ▸ advance)
  succMany?_zero a := congrArg some (Int.add_zero a)
  succMany?_add_one n a := congrArg some (Int.add_assoc a (n : Int) 1).symm

public theorem Std.PRange.instLawfulUpwardEnumerableLEInt : LawfulUpwardEnumerableLE Int where
  le_iff a b := ⟨fun h => ⟨(b - a).toNat, congrArg some (by
    change a + ((b - a).toNat : Int) = b
    rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h), Int.add_comm, Int.sub_add_cancel])⟩,
    fun h => h.elim fun n eqNext =>
      (Option.some.inj eqNext) ▸ Int.le_add_of_nonneg_right (a := a) (Int.natCast_nonneg n)⟩

private theorem reachUpper (lo hi : Int) : hi ≤ lo + ((hi - lo).toNat : Int) := by
  by_cases h : lo ≤ hi
  · rw [Int.toNat_of_nonneg (Int.sub_nonneg_of_le h), Int.add_comm, Int.sub_add_cancel]
    exact Int.le_refl _
  · exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge h)) (Int.le_add_of_nonneg_right (Int.natCast_nonneg _))

public theorem Std.PRange.instLawfulHasSizeInt : Rxc.LawfulHasSize Int where
  size_eq_zero_of_not_le lo hi h := by
    have bound : hi + 1 ≤ lo := Int.lt_of_not_ge h
    exact Int.toNat_of_nonpos (Int.sub_nonpos_of_le bound)
  size_eq_one_of_succ?_eq_none lo _ _ h :=
    False.elim (Option.noConfusion rfl (heq_of_eq (show some (lo + 1) = none from h)))
  size_eq_succ_of_succ?_eq_some lo hi lo' h next := by
    have eq : lo + 1 = lo' := Option.some.inj next
    subst lo'
    change (hi + 1 - lo).toNat = (hi + 1 - (lo + 1)).toNat + 1
    have shift : hi + 1 - lo = (hi - lo) + 1 := Int.add_right_comm hi 1 (-lo)
    rw [Int.add_sub_add_right, shift]
    exact Int.toNat_add (Int.sub_nonneg_of_le h) (Int.le_of_lt (Int.zero_lt_one))

public theorem Std.PRange.instIsAlwaysFiniteInt_1 : Rxo.IsAlwaysFinite Int :=
  ⟨fun lo hi => ⟨(hi - lo).toNat, Int.not_lt_of_ge (reachUpper lo hi)⟩⟩

public theorem Std.PRange.instIsAlwaysFiniteInt : Rxc.IsAlwaysFinite Int :=
  ⟨fun lo hi => ⟨((hi + 1) - lo).toNat, Int.not_le_of_gt (reachUpper lo (hi + 1))⟩⟩

end OmegaChecks.InitPort.Alternatives
