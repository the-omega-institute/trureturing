module
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.Int
public import Init.Data.Range.Polymorphic.Fin
public import Init.Data.Range.Polymorphic.UInt
import all Init.Data.Range.Polymorphic.Internal.SignedBitVec
import all Init.Data.Range.Polymorphic.SInt
import Init.Data.BitVec.Lemmas

/-! Successor and size laws for ranges of naturals, integers, and finite indices. -/

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

private theorem enumerableImage {α β : Type u} [UpwardEnumerable α] [UpwardEnumerable β]
    [LawfulUpwardEnumerable α] (f : α → β) (g : β → α)
    (left : ∀ a, g (f a) = a) (right : ∀ b, f (g b) = b)
    (next : ∀ a, succ? (f a) = (succ? a).map f)
    (many : ∀ k a, succMany? k (f a) = (succMany? k a).map f) :
    LawfulUpwardEnumerable β where
  ne_of_lt a _ := by
    rintro ⟨n, reaches⟩ rfl
    generalize ha : g a = x
    have eq : f x = a := ha ▸ right a
    rw [← eq, many] at reaches
    cases hs : succMany? (n + 1) x with
    | none => rw [hs] at reaches; cases reaches
    | some y =>
      rw [hs] at reaches
      have same := (left y).symm.trans ((congrArg g (Option.some.inj reaches)).trans (left x))
      exact LawfulUpwardEnumerable.ne_of_lt _ _ ⟨n, hs⟩ same.symm
  succMany?_zero b := by
    rw [← right b, many, LawfulUpwardEnumerable.succMany?_zero]
    rfl
  succMany?_add_one k b := by
    generalize h : g b = a
    have eq : f a = b := h ▸ right b
    rw [← eq, many, many, LawfulUpwardEnumerable.succMany?_add_one]
    cases middle : succMany? k a with
    | none => rfl
    | some y => exact (next y).symm

private theorem closedSizeImage {α β : Type u} [UpwardEnumerable α] [UpwardEnumerable β]
    [LE α] [LE β] [Rxc.HasSize α] [Rxc.HasSize β] [Rxc.LawfulHasSize α]
    (f : α → β) (g : β → α) (left : ∀ a, g (f a) = a) (right : ∀ b, f (g b) = b)
    (next : ∀ a, succ? (f a) = (succ? a).map f)
    (le : ∀ a b, a ≤ b ↔ g a ≤ g b)
    (size : ∀ a b, Rxc.HasSize.size a b = Rxc.HasSize.size (g a) (g b)) :
    Rxc.LawfulHasSize β where
  size_eq_zero_of_not_le a b denied := (size a b).trans
    (Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ fun h => denied ((le a b).mpr h))
  size_eq_one_of_succ?_eq_none a b h stop := by
    have eq := (next (g a)).symm.trans ((congrArg succ? (right a)).trans stop)
    have noneEq : succ? (g a) = none := by
      cases hs : succ? (g a) with
      | none => rfl
      | some x => rw [hs] at eq; cases eq
    exact (size a b).trans (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((le a b).mp h) noneEq)
  size_eq_succ_of_succ?_eq_some a b c h step := by
    have eq := (next (g a)).symm.trans ((congrArg succ? (right a)).trans step)
    have someEq : succ? (g a) = some (g c) := by
      cases hs : succ? (g a) with
      | none => rw [hs] at eq; cases eq
      | some x =>
        rw [hs] at eq
        exact congrArg some ((left x).symm.trans (congrArg g (Option.some.inj eq)))
    exact (size a b).trans ((Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((le a b).mp h) someEq).trans
      (congrArg Nat.succ (size c b).symm))

public theorem UInt8.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt8 :=
  enumerableImage UInt8.ofBitVec UInt8.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt8.succ?_ofBitVec) (fun _ _ => UInt8.succMany?_ofBitVec)

public theorem UInt8.instLawfulHasSize : Rxc.LawfulHasSize UInt8 :=
  closedSizeImage UInt8.ofBitVec UInt8.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt8.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt16.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt16 :=
  enumerableImage UInt16.ofBitVec UInt16.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt16.succ?_ofBitVec) (fun _ _ => UInt16.succMany?_ofBitVec)

public theorem UInt16.instLawfulHasSize : Rxc.LawfulHasSize UInt16 :=
  closedSizeImage UInt16.ofBitVec UInt16.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt16.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt32.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt32 :=
  enumerableImage UInt32.ofBitVec UInt32.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt32.succ?_ofBitVec) (fun _ _ => UInt32.succMany?_ofBitVec)

public theorem UInt32.instLawfulHasSize : Rxc.LawfulHasSize UInt32 :=
  closedSizeImage UInt32.ofBitVec UInt32.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt32.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem UInt64.instLawfulUpwardEnumerable : LawfulUpwardEnumerable UInt64 :=
  enumerableImage UInt64.ofBitVec UInt64.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt64.succ?_ofBitVec) (fun _ _ => UInt64.succMany?_ofBitVec)

public theorem UInt64.instLawfulHasSize : Rxc.LawfulHasSize UInt64 :=
  closedSizeImage UInt64.ofBitVec UInt64.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => UInt64.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem USize.instLawfulUpwardEnumerable : LawfulUpwardEnumerable USize :=
  enumerableImage USize.ofBitVec USize.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => USize.succ?_ofBitVec) (fun _ _ => USize.succMany?_ofBitVec)

public theorem USize.instLawfulHasSize : Rxc.LawfulHasSize USize :=
  closedSizeImage USize.ofBitVec USize.toBitVec (fun _ => rfl) (fun _ => rfl)
    (fun _ => USize.succ?_ofBitVec) (fun _ _ => Iff.rfl) (fun _ _ => rfl)

public theorem BitVec.Signed.rotate_map_eq_iff :
    type_of% (private_decl% @_root_.BitVec.Signed.rotate_map_eq_iff) := by
  intro n x y
  cases x <;> cases y
  · exact Iff.rfl
  · exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  · exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  · exact ⟨fun h => congrArg some (_root_.BitVec.Signed.rotate_eq_iff.mp (Option.some.inj h)),
      fun h => congrArg some (_root_.BitVec.Signed.rotate_eq_iff.mpr (Option.some.inj h))⟩

public theorem BitVec.Signed.instLawfulUpwardEnumerable :
    type_of% (private_decl% @_root_.BitVec.Signed.instLawfulUpwardEnumerable) := by
  intro w
  exact @enumerableImage (BitVec w) (BitVec w) _root_.BitVec.instUpwardEnumerable
    _root_.BitVec.Signed.instUpwardEnumerable BitVec.instLawfulUpwardEnumerable
    _root_.BitVec.Signed.rotate _root_.BitVec.Signed.rotate (fun _ => _root_.BitVec.Signed.rotate_rotate)
    (fun _ => _root_.BitVec.Signed.rotate_rotate) (fun _ => _root_.BitVec.Signed.succ?_rotate)
    (fun _ _ => _root_.BitVec.Signed.succMany?_rotate)

private theorem closedOfFiniteEnumeration {α : Type u} [UpwardEnumerable α] [LE α]
    (finite : Rxi.IsAlwaysFinite α) : Rxc.IsAlwaysFinite α where
  finite lo _ := by
    obtain ⟨n, stop⟩ := finite.finite lo
    exact ⟨n, by rw [stop]; exact True.intro⟩

private theorem openOfFiniteEnumeration {α : Type u} [UpwardEnumerable α] [LT α]
    (finite : Rxi.IsAlwaysFinite α) : Rxo.IsAlwaysFinite α where
  finite lo _ := by
    obtain ⟨n, stop⟩ := finite.finite lo
    exact ⟨n, by rw [stop]; exact True.intro⟩

public theorem Int8.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int8 where
  finite a := by
    refine ⟨(_root_.Int8.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int8.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int8 :=
  closedOfFiniteEnumeration Int8.instRxiIsAlwaysFinite

public theorem Int8.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int8 :=
  openOfFiniteEnumeration Int8.instRxiIsAlwaysFinite

public theorem Int16.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int16 where
  finite a := by
    refine ⟨(_root_.Int16.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int16.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int16 :=
  closedOfFiniteEnumeration Int16.instRxiIsAlwaysFinite

public theorem Int16.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int16 :=
  openOfFiniteEnumeration Int16.instRxiIsAlwaysFinite

public theorem Int32.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int32 where
  finite a := by
    refine ⟨(_root_.Int32.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int32.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int32 :=
  closedOfFiniteEnumeration Int32.instRxiIsAlwaysFinite

public theorem Int32.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int32 :=
  openOfFiniteEnumeration Int32.instRxiIsAlwaysFinite

public theorem Int64.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite Int64 where
  finite a := by
    refine ⟨(_root_.Int64.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem Int64.instIsAlwaysFinite : Rxc.IsAlwaysFinite Int64 :=
  closedOfFiniteEnumeration Int64.instRxiIsAlwaysFinite

public theorem Int64.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite Int64 :=
  openOfFiniteEnumeration Int64.instRxiIsAlwaysFinite

public theorem ISize.instRxiIsAlwaysFinite : Rxi.IsAlwaysFinite ISize where
  finite a := by
    refine ⟨(_root_.ISize.maxValueSealed.toInt - a.toInt).toNat + 1, ?_⟩
    apply dite_eq_right
    omega

public theorem ISize.instIsAlwaysFinite : Rxc.IsAlwaysFinite ISize :=
  closedOfFiniteEnumeration ISize.instRxiIsAlwaysFinite

public theorem ISize.instRxoIsAlwaysFinite : Rxo.IsAlwaysFinite ISize :=
  openOfFiniteEnumeration ISize.instRxiIsAlwaysFinite

private theorem signedSizeLaws {α : Type u} [UpwardEnumerable α] [LE α] [LT α]
    [Rxc.HasSize α] [Rxo.HasSize α] [Rxi.HasSize α]
    (value : α → Int) (limit : Int) (below : ∀ x, value x < limit)
    (le : ∀ a b, a ≤ b ↔ value a ≤ value b) (lt : ∀ a b, a < b ↔ value a < value b)
    (closedSize : ∀ a b, Rxc.HasSize.size a b = (value b + 1 - value a).toNat)
    (openSize : ∀ a b, Rxo.HasSize.size a b = (value b + 1 - value a).toNat - 1)
    (tailSize : ∀ a, Rxi.HasSize.size a = (limit - value a).toNat)
    (endStep : ∀ a, value a = limit - 1 → succ? a = none)
    (nextStep : ∀ a, value a < limit - 1 → ∃ b, succ? a = some b ∧ value b = value a + 1) :
    Rxc.LawfulHasSize α ∧ Rxo.LawfulHasSize α ∧ Rxi.LawfulHasSize α := by
  have stop {a} (h : succ? a = none) : value a = limit - 1 := by
    by_cases before : value a < limit - 1
    · obtain ⟨_, step, _⟩ := nextStep a before
      rw [h] at step
      cases step
    · have bound := below a
      omega
  have inc {a b} (h : succ? a = some b) : value b = value a + 1 := by
    by_cases last : value a = limit - 1
    · rw [endStep a last] at h
      cases h
    · have bound := below a
      obtain ⟨_, found, eq⟩ := nextStep a (by omega)
      cases Option.some.inj (found.symm.trans h)
      exact eq
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a b denied
    rw [closedSize]
    have h : ¬ value a ≤ value b := fun p => denied ((le a b).mpr p)
    exact Int.toNat_eq_zero.mpr (by omega)
  · intro a b ok stopped
    rw [closedSize]
    have eq := stop stopped
    have lower := (le a b).mp ok
    have upper := below b
    omega
  · intro a b c ok step
    rw [closedSize, closedSize]
    have eq := inc step
    have lower := (le a b).mp ok
    omega
  · intro a b denied
    rw [openSize]
    have h : ¬value a < value b := fun p => denied ((lt a b).mpr p)
    omega
  · intro a b ok stopped
    have eq := stop stopped
    have lower := (lt a b).mp ok
    have upper := below b
    omega
  · intro a b c ok step
    rw [openSize, openSize]
    have eq := inc step
    have lower := (lt a b).mp ok
    omega
  · intro a stopped
    rw [tailSize]
    have eq := stop stopped
    omega
  · intro a b step
    rw [tailSize, tailSize]
    have eq := inc step
    have upper := below b
    omega

private theorem signedPowerSizes {α : Type u} [UpwardEnumerable α] [LE α] [LT α] [DecidableEq α]
    [Rxc.HasSize α] [Rxo.HasSize α] [Rxi.HasSize α]
    (value : α → Int) (k : Nat) (low : α) (addOne : α → α)
    (inj : ∀ {a b}, value a = value b → a = b)
    (below : ∀ a, value a < (2 : Int)^k) (above : ∀ a, -(2 : Int)^k ≤ value a)
    (minValue : value low = -(2 : Int)^k)
    (addValue : ∀ a, value (addOne a) = (value a + 1).bmod (2^(k+1)))
    (next : ∀ a, succ? a = if addOne a = low then none else some (addOne a))
    (le : ∀ a b, a ≤ b ↔ value a ≤ value b) (lt : ∀ a b, a < b ↔ value a < value b)
    (closedSize : ∀ a b, Rxc.HasSize.size a b = (value b + 1 - value a).toNat)
    (openSize : ∀ a b, Rxo.HasSize.size a b = (value b + 1 - value a).toNat - 1)
    (tailSize : ∀ a, Rxi.HasSize.size a = ((2 : Int)^k - value a).toNat) :
    Rxc.LawfulHasSize α ∧ Rxo.LawfulHasSize α ∧ Rxi.LawfulHasSize α := by
  let half := 2^k
  have pos : 0 < half := Nat.two_pow_pos k
  have cast : (2 : Int)^k = (half : Int) := (Int.natCast_pow 2 k).symm
  have full : 2^(k+1) = half + half := (Nat.pow_succ 2 k).trans (Nat.mul_two _)
  apply signedSizeLaws value ((2 : Int)^k) below le lt closedSize openSize tailSize
  · intro a last
    rw [next]
    apply ite_eq_left
    apply inj
    rw [addValue, full, minValue, cast]
    rw [cast] at last
    calc
      _ = (-(half : Int) + ↑(half + half)).bmod (half + half) :=
        congrArg (fun z : Int => z.bmod (half + half)) (by omega)
      _ = (-(half : Int)).bmod (half + half) := Int.add_bmod_right _ _
      _ = _ := Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  · intro a before
    have lowBound := above a
    rw [cast] at before lowBound
    have eq : value (addOne a) = value a + 1 := by
      rw [addValue, full]
      exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
    refine ⟨addOne a, ?_, eq⟩
    rw [next]
    apply ite_eq_right
    intro wrap
    have bad := eq.symm.trans ((congrArg value wrap).trans (minValue.trans (congrArg Neg.neg cast)))
    omega

private theorem Int8SizeLaws : Rxc.LawfulHasSize Int8 ∧ Rxo.LawfulHasSize Int8 ∧ Rxi.LawfulHasSize Int8 := by
  apply signedPowerSizes Int8.toInt 7 _root_.Int8.minValueSealed (· + 1) Int8.toInt.inj
    Int8.toInt_lt Int8.le_toInt
    ((congrArg Int8.toInt _root_.Int8.minValueSealed_def).trans Int8.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int8.le_iff_toInt_le) (fun _ _ => Int8.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int8.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int8.toInt 1 = 1 from rfl))

public theorem Int8.instRxcLawfulHasSize : Rxc.LawfulHasSize Int8 := Int8SizeLaws.1
public theorem Int8.instRxoLawfulHasSize : Rxo.LawfulHasSize Int8 := Int8SizeLaws.2.1
public theorem Int8.instRxiLawfulHasSize : Rxi.LawfulHasSize Int8 := Int8SizeLaws.2.2

private theorem Int16SizeLaws : Rxc.LawfulHasSize Int16 ∧ Rxo.LawfulHasSize Int16 ∧ Rxi.LawfulHasSize Int16 := by
  apply signedPowerSizes Int16.toInt 15 _root_.Int16.minValueSealed (· + 1) Int16.toInt.inj
    Int16.toInt_lt Int16.le_toInt
    ((congrArg Int16.toInt _root_.Int16.minValueSealed_def).trans Int16.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int16.le_iff_toInt_le) (fun _ _ => Int16.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int16.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int16.toInt 1 = 1 from rfl))

public theorem Int16.instRxcLawfulHasSize : Rxc.LawfulHasSize Int16 := Int16SizeLaws.1
public theorem Int16.instRxoLawfulHasSize : Rxo.LawfulHasSize Int16 := Int16SizeLaws.2.1
public theorem Int16.instRxiLawfulHasSize : Rxi.LawfulHasSize Int16 := Int16SizeLaws.2.2

private theorem Int32SizeLaws : Rxc.LawfulHasSize Int32 ∧ Rxo.LawfulHasSize Int32 ∧ Rxi.LawfulHasSize Int32 := by
  apply signedPowerSizes Int32.toInt 31 _root_.Int32.minValueSealed (· + 1) Int32.toInt.inj
    Int32.toInt_lt Int32.le_toInt
    ((congrArg Int32.toInt _root_.Int32.minValueSealed_def).trans Int32.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int32.le_iff_toInt_le) (fun _ _ => Int32.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int32.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int32.toInt 1 = 1 from rfl))

public theorem Int32.instRxcLawfulHasSize : Rxc.LawfulHasSize Int32 := Int32SizeLaws.1
public theorem Int32.instRxoLawfulHasSize : Rxo.LawfulHasSize Int32 := Int32SizeLaws.2.1
public theorem Int32.instRxiLawfulHasSize : Rxi.LawfulHasSize Int32 := Int32SizeLaws.2.2

private theorem Int64SizeLaws : Rxc.LawfulHasSize Int64 ∧ Rxo.LawfulHasSize Int64 ∧ Rxi.LawfulHasSize Int64 := by
  apply signedPowerSizes Int64.toInt 63 _root_.Int64.minValueSealed (· + 1) Int64.toInt.inj
    Int64.toInt_lt Int64.le_toInt
    ((congrArg Int64.toInt _root_.Int64.minValueSealed_def).trans Int64.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => Int64.le_iff_toInt_le) (fun _ _ => Int64.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  exact (Int64.toInt_add _ _).trans (congrArg (fun z : Int => (a.toInt + z).bmod _) (show Int64.toInt 1 = 1 from rfl))

public theorem Int64.instRxcLawfulHasSize : Rxc.LawfulHasSize Int64 := Int64SizeLaws.1
public theorem Int64.instRxoLawfulHasSize : Rxo.LawfulHasSize Int64 := Int64SizeLaws.2.1
public theorem Int64.instRxiLawfulHasSize : Rxi.LawfulHasSize Int64 := Int64SizeLaws.2.2

private theorem ISizeSizeLaws : Rxc.LawfulHasSize ISize ∧ Rxo.LawfulHasSize ISize ∧ Rxi.LawfulHasSize ISize := by
  apply signedPowerSizes ISize.toInt (System.Platform.numBits - 1) _root_.ISize.minValueSealed (· + 1) ISize.toInt.inj
    ISize.toInt_lt_two_pow_numBits ISize.two_pow_numBits_le_toInt
    ((congrArg ISize.toInt _root_.ISize.minValueSealed_def).trans ISize.toInt_minValue) ?_
    (fun _ => rfl) (fun _ _ => ISize.le_iff_toInt_le) (fun _ _ => ISize.lt_iff_toInt_lt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  intro a
  rw [ISize.toInt_add, show ISize.toInt 1 = 1 from ISize.toInt_ofNat_of_lt (by decide),
    Nat.sub_add_cancel System.Platform.numBits_pos]

public theorem ISize.instRxcLawfulHasSize : Rxc.LawfulHasSize ISize := ISizeSizeLaws.1
public theorem ISize.instRxoLawfulHasSize : Rxo.LawfulHasSize ISize := ISizeSizeLaws.2.1
public theorem ISize.instRxiLawfulHasSize : Rxi.LawfulHasSize ISize := ISizeSizeLaws.2.2

end OmegaChecks.InitPort.Alternatives
