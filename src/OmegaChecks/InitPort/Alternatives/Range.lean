module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int

/-! Direct witnesses for finite natural ranges and their successor law. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

/-- Split the intermediate result before applying the successor law. This establishes
the bind equation at the given element without identifying two functions. -/
public theorem Std.PRange.UpwardEnumerable.succMany?_add
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] {m n : Nat} {a : α} :
    succMany? (m + n) a = (succMany? m a).bind (succMany? n ·) := by
  induction n with
  | zero =>
    cases succMany? m a with
    | none => rfl
    | some b => exact (_root_.Std.PRange.UpwardEnumerable.succMany?_zero (a := b)).symm
  | succ n ih =>
    rw [← Nat.add_assoc, _root_.Std.PRange.UpwardEnumerable.succMany?_add_one, ih]
    cases succMany? m a with
    | none => rfl
    | some b => exact (_root_.Std.PRange.UpwardEnumerable.succMany?_add_one (a := b)).symm

public theorem Std.PRange.UpwardEnumerable.le_of_lt : type_of% @_root_.Std.PRange.UpwardEnumerable.le_of_lt :=
  fun h => h.elim fun n eq => ⟨n + 1, eq⟩

public theorem Std.PRange.UpwardEnumerable.le_trans : type_of% @_root_.Std.PRange.UpwardEnumerable.le_trans := by
  intro α inst law a b c hab hbc
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  exact ⟨m+n, (Std.PRange.UpwardEnumerable.succMany?_add.trans
    (congrArg (fun o => o.bind (succMany? n ·)) hm)).trans hn⟩

public theorem Std.PRange.UpwardEnumerable.lt_of_le_of_lt :
    type_of% @_root_.Std.PRange.UpwardEnumerable.lt_of_le_of_lt := by
  intro α inst law a b c hab hbc
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  refine ⟨m+n, ?_⟩
  rw [Nat.add_assoc, Std.PRange.UpwardEnumerable.succMany?_add (m := m) (n := n+1), hm]
  exact hn

public theorem Std.PRange.UpwardEnumerable.lt_of_lt_of_le :
    type_of% @_root_.Std.PRange.UpwardEnumerable.lt_of_lt_of_le := by
  intro α inst law a b c hab hbc
  obtain ⟨m, hm⟩ := hab
  obtain ⟨n, hn⟩ := hbc
  refine ⟨m+n, ?_⟩
  rw [Nat.add_right_comm m n 1, Std.PRange.UpwardEnumerable.succMany?_add, hm]
  exact hn

public theorem Std.PRange.UpwardEnumerable.lt_trans : type_of% @_root_.Std.PRange.UpwardEnumerable.lt_trans :=
  fun hab hbc => Std.PRange.UpwardEnumerable.lt_of_le_of_lt (Std.PRange.UpwardEnumerable.le_of_lt hab) hbc

public theorem Std.instLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulOrderLT :
    type_of% @_root_.Std.instLawfulUpwardEnumerableLTOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulOrderLT := by
  intro α le lt enum lawful enumLe order
  constructor
  intro a b
  constructor
  · intro h
    obtain ⟨hab, hba⟩ := (LawfulOrderLT.lt_iff a b).mp h
    exact UpwardEnumerable.lt_of_le_of_ne (UpwardEnumerable.le_iff.mp hab)
      (fun eq => hba (eq ▸ hab))
  · intro h
    exact (LawfulOrderLT.lt_iff a b).mpr ⟨UpwardEnumerable.le_iff.mpr (Std.PRange.UpwardEnumerable.le_of_lt h),
      fun hba => UpwardEnumerable.lt_irrefl (Std.PRange.UpwardEnumerable.lt_of_lt_of_le h (UpwardEnumerable.le_iff.mp hba))⟩

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

private theorem intOpenSize (lo hi : Int) : Rxo.HasSize.size lo hi = (hi - lo).toNat := by
  change (hi + 1 - lo).toNat - 1 = (hi - lo).toNat
  rw [← Int.pred_toNat]
  apply congrArg Int.toNat
  exact (congrArg (· - 1) (Int.add_right_comm hi 1 (-lo))).trans (Int.add_sub_cancel ..)

public theorem Std.PRange.instLawfulHasSizeInt_1 : Rxo.LawfulHasSize Int where
  size_eq_zero_of_not_le lo hi h := (intOpenSize lo hi).trans (Int.toNat_of_nonpos (Int.sub_nonpos_of_le (Int.le_of_not_gt h)))
  size_eq_one_of_succ?_eq_none lo _ _ h :=
    False.elim (Option.noConfusion rfl (heq_of_eq (show some (lo + 1) = none from h)))
  size_eq_succ_of_succ?_eq_some lo hi lo' h next := by
    have eq : lo + 1 = lo' := Option.some.inj next
    subst lo'
    rw [intOpenSize, intOpenSize]
    have diff : hi - (lo + 1) + 1 = hi - lo := by
      rw [← Int.sub_sub, Int.sub_add_cancel]
    exact (congrArg Int.toNat diff.symm).trans
      (Int.toNat_add (Int.sub_nonneg_of_le h) (Int.le_of_lt Int.zero_lt_one))

public theorem Std.PRange.instIsAlwaysFiniteInt_1 : Rxo.IsAlwaysFinite Int :=
  ⟨fun lo hi => ⟨(hi - lo).toNat, Int.not_lt_of_ge (reachUpper lo hi)⟩⟩

public theorem Std.PRange.instIsAlwaysFiniteInt : Rxc.IsAlwaysFinite Int :=
  ⟨fun lo hi => ⟨((hi + 1) - lo).toNat, Int.not_le_of_gt (reachUpper lo (hi + 1))⟩⟩

end OmegaChecks.InitPort.Alternatives
