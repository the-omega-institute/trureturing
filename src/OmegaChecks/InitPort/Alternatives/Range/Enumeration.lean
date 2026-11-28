module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Fin
import all Init.Data.Range.Polymorphic.Fin
public import Init.Data.Range.Polymorphic.UInt
import all Init.Data.Range.Polymorphic.Internal.SignedBitVec
import all Init.Data.Range.Polymorphic.SInt
import all Init.Data.Char.Ordinal
import all Init.Data.Range.Polymorphic.Char
import Init.Data.BitVec.Lemmas

/-! Successors and sizes of natural, integer and bit-vector ranges. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.PRange.UpwardEnumerable.isSome_least? :
    type_of% @_root_.Std.PRange.UpwardEnumerable.isSome_least? := by
  intro α _ _ _ hn
  obtain ⟨a⟩ := hn
  obtain ⟨b, h, _⟩ := _root_.Std.PRange.UpwardEnumerable.least?_le (a := a)
  rw [h]
  rfl

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

public theorem Std.PRange.UpwardEnumerable.le_iff_lt_or_eq :
    type_of% @_root_.Std.PRange.UpwardEnumerable.le_iff_lt_or_eq := by
  intro α en law a b
  constructor
  · rintro ⟨k, h⟩
    cases k with
    | zero => exact Or.inr (Option.some.inj (_root_.Std.PRange.UpwardEnumerable.succMany?_zero.symm.trans h))
    | succ k => exact Or.inl ⟨k, h⟩
  · rintro (lt | rfl)
    · exact Std.PRange.UpwardEnumerable.le_of_lt lt
    · exact ⟨0, _root_.Std.PRange.UpwardEnumerable.succMany?_zero⟩

public theorem Fin.instLawfulUpwardEnumerableLE {n : Nat} : LawfulUpwardEnumerableLE (Fin n) where
  le_iff a b := by
    constructor
    · intro le
      have dist : a.val + (b.val - a.val) = b.val := Nat.add_sub_of_le le
      exact ⟨b.val - a.val, _root_.Fin.addNat?_eq_some_iff.mpr ⟨dist.symm ▸ b.isLt, dist.symm⟩⟩
    · rintro ⟨k, reached⟩
      have eq := (_root_.Fin.addNat?_eq_some_iff.mp reached).2
      change a.val ≤ b.val
      rw [eq]
      exact Nat.le_add_right a.val k

public theorem Fin.instLawfulUpwardEnumerable {n : Nat} : LawfulUpwardEnumerable (Fin n) where
  ne_of_lt a b := by
    rintro ⟨k, reached⟩ rfl
    have impossible := (_root_.Fin.addNat?_eq_some_iff.mp reached).2
    omega
  succMany?_zero _ := _root_.Fin.addNat?_zero
  succMany?_add_one k a := by
    change a.addNat? (k + 1) = (a.addNat? k).bind (fun b => b.addNat? 1)
    cases mid : a.addNat? k with
    | none =>
      have limit := _root_.Fin.addNat?_eq_none_iff.mp mid
      exact _root_.Fin.addNat?_eq_none_iff.mpr (by omega)
    | some b =>
      have eq := (_root_.Fin.addNat?_eq_some_iff.mp mid).2
      by_cases last : b.val + 1 < n
      · exact ((_root_.Fin.addNat?_eq_some_iff (j := ⟨b.val + 1, last⟩)).mpr
          ⟨by omega, by change b.val + 1 = a.val + (k + 1); omega⟩).trans
          (_root_.Fin.addNat?_eq_some last).symm
      · exact (_root_.Fin.addNat?_eq_none_iff.mpr (by omega)).trans
          (_root_.Fin.addNat?_eq_none_iff.mpr (by omega)).symm

public theorem Fin.instLawfulHasSize_2 {n : Nat} : Rxi.LawfulHasSize (Fin n) where
  size_eq_one_of_succ?_eq_none a h := by
    have stop := _root_.Fin.addNat?_eq_none_iff.mp h
    change n - a.val = 1
    have below := a.isLt
    omega
  size_eq_succ_of_succ?_eq_some a b h := by
    have eq := (_root_.Fin.addNat?_eq_some_iff.mp h).2
    change n - a.val = n - b.val + 1
    have below := b.isLt
    omega

public theorem Fin.instLawfulUpwardEnumerableLE._proof_6 :
    type_of% (private_decl% @_root_.Fin.instLawfulUpwardEnumerableLE._proof_6) := by
  intro n x y le
  have dist := Nat.add_sub_of_le le
  exact ⟨dist.symm ▸ y.isLt, dist⟩

public theorem Fin.instLawfulUpwardEnumerableLE._proof_7 :
    type_of% (private_decl% @_root_.Fin.instLawfulUpwardEnumerableLE._proof_7) := by
  rintro n x y ⟨k, _, distance⟩
  exact distance ▸ Nat.le_add_right x.val k

public theorem Fin.instLawfulUpwardEnumerable._proof_3 :
    type_of% (private_decl% @_root_.Fin.instLawfulUpwardEnumerable._proof_3) :=
  fun {_} => Fin.instLawfulUpwardEnumerable.ne_of_lt

public theorem Fin.instLawfulUpwardEnumerable._proof_7 :
    type_of% (private_decl% @_root_.Fin.instLawfulUpwardEnumerable._proof_7) :=
  fun {_} => Fin.instLawfulUpwardEnumerable.succMany?_add_one

public theorem Fin.instLawfulHasSize_2._proof_2 :
    type_of% (private_decl% @_root_.Fin.instLawfulHasSize_2._proof_2) :=
  fun {_} => Fin.instLawfulHasSize_2.size_eq_one_of_succ?_eq_none

public theorem Fin.instLawfulHasSize_2._proof_3 :
    type_of% (private_decl% @_root_.Fin.instLawfulHasSize_2._proof_3) :=
  fun {_} => Fin.instLawfulHasSize_2.size_eq_succ_of_succ?_eq_some

private theorem bitNextValue {w : Nat} (x : BitVec w) :
    (x + 1).toNat = (x.toNat + 1) % 2^w := by
  exact Nat.add_mod_mod _ _ _

private theorem bitAddStops {w : Nat} (x : BitVec w) :
    x + 1 = 0 ↔ x.toNat = 2 ^ w - 1 := by
  have bound : x.toNat < 2 ^ w := x.isLt
  have pos := Nat.two_pow_pos w
  constructor
  · intro eq
    by_cases beyond : 2^w ≤ x.toNat + 1
    · omega
    · have zero := congrArg BitVec.toNat eq
      rw [bitNextValue, Nat.mod_eq_of_lt (Nat.lt_of_not_ge beyond)] at zero
      change x.toNat + 1 = 0 at zero
      omega
  · intro endValue
    apply BitVec.eq_of_toNat_eq
    rw [bitNextValue, show x.toNat + 1 = 2^w by omega, Nat.mod_self]
    rfl

public theorem BitVec.succ?_eq_none : type_of% @_root_.BitVec.succ?_eq_none := by
  intro w x
  change (if x + 1 = 0 then none else some (x + 1)) = none ↔ _
  by_cases stop : x + 1 = 0
  · rw [ite_eq_left stop]
    exact ⟨fun _ => (bitAddStops x).mp stop, fun _ => rfl⟩
  · rw [ite_eq_right stop]
    exact ⟨(fun h => nomatch h), fun h => (stop ((bitAddStops x).mpr h)).elim⟩

public theorem BitVec.succ?_eq_some : type_of% @_root_.BitVec.succ?_eq_some := by
  intro w x y
  change (if x + 1 = 0 then none else some (x + 1)) = some y ↔ _
  have bound : x.toNat < 2 ^ w := x.isLt
  by_cases stop : x + 1 = 0
  · rw [ite_eq_left stop]
    have atEnd := (bitAddStops x).mp stop
    exact ⟨(fun h => nomatch h), fun ⟨lt, _⟩ => (Nat.lt_irrefl _ (atEnd ▸ lt)).elim⟩
  · rw [ite_eq_right stop]
    have before : x.toNat < 2^w - 1 := by
      exact Nat.lt_of_le_of_ne (by omega) (fun h => stop ((bitAddStops x).mpr h))
    have inc : (x + 1).toNat = x.toNat + 1 := (bitNextValue x).trans (Nat.mod_eq_of_lt (by omega))
    constructor
    · intro h
      cases Option.some.inj h
      exact ⟨before, inc⟩
    · rintro ⟨_, eq⟩
      exact congrArg some (BitVec.eq_of_toNat_eq (inc.trans eq.symm))

private theorem bitManyEq {w k : Nat} {x y : BitVec w} :
    succMany? k x = some y ↔ y.toNat = x.toNat + k := by
  change (if h : x.toNat + k < 2^w then some (BitVec.ofNatLT _ h) else none) = some y ↔ _
  by_cases inside : x.toNat + k < 2^w
  · rw [dite_eq_left inside]
    exact ⟨fun h => (congrArg BitVec.toNat (Option.some.inj h)).symm,
      fun h => congrArg some (BitVec.eq_of_toNat_eq h.symm)⟩
  · rw [dite_eq_right inside]
    exact ⟨(fun h => nomatch h), fun h => (inside (h ▸ y.isLt)).elim⟩

public theorem BitVec.instLawfulUpwardEnumerable {w : Nat} : LawfulUpwardEnumerable (BitVec w) where
  ne_of_lt a b := by
    rintro ⟨k, h⟩ rfl
    have impossible := bitManyEq.mp h
    omega
  succMany?_zero _ := bitManyEq.mpr rfl
  succMany?_add_one k a := by
    cases mid : succMany? k a with
    | none =>
      cases last : succMany? (k + 1) a with
      | none => rfl
      | some b =>
        have eq := bitManyEq.mp last
        have bound := b.isLt
        have inside : a.toNat + k < 2^w := by omega
        have found := (bitManyEq (x := a) (y := BitVec.ofNatLT _ inside) (k := k)).mpr rfl
        rw [mid] at found
        cases found
    | some b =>
      have eq := bitManyEq.mp mid
      change succMany? (k + 1) a = succ? b
      cases last : succ? b with
      | some c =>
        have inc := (BitVec.succ?_eq_some.mp last).2
        exact bitManyEq.mpr (by omega)
      | none =>
        have atEnd := BitVec.succ?_eq_none.mp last
        cases endValue : succMany? (k + 1) a with
        | none => rfl
        | some c =>
          have inc := bitManyEq.mp endValue
          have bound := c.isLt
          omega

public theorem BitVec.instRxcLawfulHasSize {w : Nat} : Rxc.LawfulHasSize (BitVec w) where
  size_eq_zero_of_not_le lo hi h := by
    change ¬lo.toNat ≤ hi.toNat at h
    change hi.toNat + 1 - lo.toNat = 0
    omega
  size_eq_one_of_succ?_eq_none lo hi le h := by
    have endValue := BitVec.succ?_eq_none.mp h
    have limit := hi.isLt
    change lo.toNat ≤ hi.toNat at le
    change hi.toNat + 1 - lo.toNat = 1
    omega
  size_eq_succ_of_succ?_eq_some lo hi b le h := by
    have inc := (BitVec.succ?_eq_some.mp h).2
    change lo.toNat ≤ hi.toNat at le
    change hi.toNat + 1 - lo.toNat = hi.toNat + 1 - b.toNat + 1
    omega

public theorem BitVec.instRxiLawfulHasSize {w : Nat} : Rxi.LawfulHasSize (BitVec w) where
  size_eq_one_of_succ?_eq_none a h := by
    have endValue := BitVec.succ?_eq_none.mp h
    have pos := Nat.two_pow_pos w
    change 2^w - a.toNat = 1
    omega
  size_eq_succ_of_succ?_eq_some a b h := by
    obtain ⟨bound, inc⟩ := BitVec.succ?_eq_some.mp h
    change 2^w - a.toNat = 2^w - b.toNat + 1
    omega

end OmegaChecks.InitPort.Alternatives
