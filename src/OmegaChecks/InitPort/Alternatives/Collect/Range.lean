module

public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Range.Polymorphic.Map

/-! Range sizes, finite enumerations and order-preserving maps. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.Rxc.size_eq_zero_iff_not_le : type_of% @_root_.Std.Rxc.size_eq_zero_iff_not_le := by
  intro α _ _ _ _ lo hi
  refine ⟨fun hzero hle => ?_, Rxc.LawfulHasSize.size_eq_zero_of_not_le lo hi⟩
  cases hs : UpwardEnumerable.succ? lo with
  | none => exact Nat.noConfusion (hzero.symm.trans
      (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hle) (h' := hs)))
  | some next => exact Nat.noConfusion (hzero.symm.trans
      (Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs)))

public theorem Std.Rxo.size_eq_zero_iff_not_le : type_of% @_root_.Std.Rxo.size_eq_zero_iff_not_le := by
  intro α _ _ _ _ lo hi
  refine ⟨fun hzero hlt => ?_, Rxo.LawfulHasSize.size_eq_zero_of_not_le lo hi⟩
  cases hs : UpwardEnumerable.succ? lo with
  | none => exact Nat.noConfusion (hzero.symm.trans
      (Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hlt) (h' := hs)))
  | some next => exact Nat.noConfusion (hzero.symm.trans
      (Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hlt) (h' := hs)))

private theorem finiteRangeOfSize [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    (within : α → Prop) (size : α → Nat)
    (zero : ∀ lo, size lo = 0 ↔ ¬ within lo)
    (step : ∀ lo next, within lo → UpwardEnumerable.succ? lo = some next → size lo = size next + 1)
    (lo : α) : (UpwardEnumerable.succMany? (size lo) lo).elim True (fun a => ¬ within a) := by
  generalize hn : size lo = n
  induction n generalizing lo with
  | zero =>
    rw [UpwardEnumerable.succMany?_zero]
    exact (zero lo).mp hn
  | succ n ih =>
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact True.intro
    | some next =>
      apply ih
      apply Decidable.byContradiction
      intro hne
      have outside : ¬ within lo := fun h => hne (Nat.succ.inj ((step lo next h hs).symm.trans hn))
      exact Nat.noConfusion (((zero lo).mpr outside).symm.trans hn)

public theorem Std.Rxc.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxc.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  refine ⟨fun lo hi => ⟨Rxc.HasSize.size lo hi, ?_⟩⟩
  exact finiteRangeOfSize (· ≤ hi) (fun a => Rxc.HasSize.size a hi)
    (fun _ => _root_.Std.Rxc.size_eq_zero_iff_not_le)
    (fun a b => Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some a hi b) lo

public theorem Std.Rxo.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxo.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  refine ⟨fun lo hi => ⟨Rxo.HasSize.size lo hi, ?_⟩⟩
  exact finiteRangeOfSize (· < hi) (fun a => Rxo.HasSize.size a hi)
    (fun _ => _root_.Std.Rxo.size_eq_zero_iff_not_le)
    (fun a b => Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some a hi b) lo

public theorem Std.Rxi.instIsAlwaysFiniteOfLawfulHasSize :
    type_of% @_root_.Std.Rxi.instIsAlwaysFiniteOfLawfulHasSize := by
  intro α _ _ _ _ _
  constructor
  intro lo
  refine ⟨Rxi.HasSize.size lo, ?_⟩
  generalize hn : Rxi.HasSize.size lo = n
  induction n generalizing lo with
  | zero =>
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact Nat.noConfusion (hn.symm.trans (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none lo hs))
    | some next => exact Nat.noConfusion (hn.symm.trans (Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo next hs))
  | succ n ih =>
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases hs : UpwardEnumerable.succ? lo with
    | none => rfl
    | some next => exact ih next (Nat.succ.inj ((Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo next hs).symm.trans hn))

public theorem Std.Rxo.LawfulHasSize.of_closed :
    type_of% @_root_.Std.Rxo.LawfulHasSize.of_closed := by
  intro α _ _ _ _ _ _ _ _ _ _ _
  letI : _root_.Std.Rxo.HasSize α := _root_.Std.Rxo.HasSize.ofClosed
  constructor
  · intro lo hi hnlt
    change Rxc.HasSize.size lo hi - 1 = 0
    by_cases hle : lo ≤ hi
    · cases hs : UpwardEnumerable.succ? lo with
      | none => rw [Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (h := hle) (h' := hs)]
      | some b =>
        have hlt : lo < b := UpwardEnumerable.lt_iff.mpr ⟨0,
          (UpwardEnumerable.succMany?_one (a := lo)).trans hs⟩
        have hnle : ¬ b ≤ hi := fun hb => hnlt (lt_of_lt_of_le hlt hb)
        rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs),
          Rxc.LawfulHasSize.size_eq_zero_of_not_le (h := hnle)]
    · rw [Rxc.LawfulHasSize.size_eq_zero_of_not_le (h := hle)]
  · intro lo hi hlt hs
    obtain ⟨n, hn⟩ := UpwardEnumerable.lt_iff.mp hlt
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hn
    cases hn
  · intro lo hi next hlt hs
    change Rxc.HasSize.size lo hi - 1 = Rxc.HasSize.size next hi - 1 + 1
    have hle := le_of_lt hlt
    obtain ⟨n, hn⟩ := UpwardEnumerable.lt_iff.mp hlt
    rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hn
    have hnext : next ≤ hi := UpwardEnumerable.le_iff.mpr ⟨n, hn⟩
    have hpos := Nat.pos_of_ne_zero fun h => (_root_.Std.Rxc.size_eq_zero_iff_not_le.mp h) hnext
    rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (h := hle) (h' := hs)]
    exact (Nat.sub_add_cancel hpos).symm

section RangeMap

open Std.PRange.UpwardEnumerable
variable {α : Type u} {β : Type v} [UpwardEnumerable α] [UpwardEnumerable β]

public theorem Std.PRange.LawfulUpwardEnumerable.ofMap.{b, a} {α : Type a} {β : Type b}
    [UpwardEnumerable α] [UpwardEnumerable β] [LawfulUpwardEnumerable β] (f : Map α β) :
    LawfulUpwardEnumerable α where
  ne_of_lt a b h eq := LawfulUpwardEnumerable.ne_of_lt _ _ (f.lt_iff.mp h) (congrArg f.toFun eq)
  succMany?_zero a := by
    apply Option.map_injective f.injective
    exact (f.succMany?_toFun _ _).symm.trans (LawfulUpwardEnumerable.succMany?_zero _)
  succMany?_add_one n a := by
    apply Option.map_injective f.injective
    rw [← f.succMany?_toFun, LawfulUpwardEnumerable.succMany?_add_one, f.succMany?_toFun]
    cases heq : succMany? n a with
    | none => rfl
    | some b => exact f.succ?_toFun b

public theorem Std.PRange.instPreservesLTOfLawfulOrderLTOfPreservesLE
    [LE α] [LT α] [LawfulOrderLT α] [LE β] [LT β] [LawfulOrderLT β] (f : Map α β)
    [f.PreservesLE] : f.PreservesLT where
  lt_iff := by
    refine (LawfulOrderLT.lt_iff _ _).trans (Iff.trans ?_ (LawfulOrderLT.lt_iff _ _).symm)
    exact ⟨fun ⟨hab, hnba⟩ => ⟨(Map.PreservesLE.le_iff (f := f)).mp hab,
      fun h => hnba ((Map.PreservesLE.le_iff (f := f)).mpr h)⟩,
      fun ⟨hab, hnba⟩ => ⟨(Map.PreservesLE.le_iff (f := f)).mpr hab,
      fun h => hnba ((Map.PreservesLE.le_iff (f := f)).mp h)⟩⟩

public theorem Std.PRange.LawfulUpwardEnumerableLE.ofMap [LE α] [LE β]
    [LawfulUpwardEnumerableLE β] (f : Map α β) [f.PreservesLE] :
    LawfulUpwardEnumerableLE α where
  le_iff _ _ := (Map.PreservesLE.le_iff (f := f)).trans
    ((LawfulUpwardEnumerableLE.le_iff _ _).trans f.le_iff.symm)

public theorem Std.Rxc.LawfulHasSize.ofMap [LE α] [LE β] [Rxc.HasSize α] [Rxc.HasSize β]
    [Rxc.LawfulHasSize β] (f : Map α β) [f.PreservesLE] [f.PreservesRxcSize] : Rxc.LawfulHasSize α where
  size_eq_zero_of_not_le _ _ h := (Map.PreservesRxcSize.size_eq (f := f)).trans
    (Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ (fun h' => h ((Map.PreservesLE.le_iff (f := f)).mpr h')))
  size_eq_one_of_succ?_eq_none _ _ h hs := (Map.PreservesRxcSize.size_eq (f := f)).trans
    (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((Map.PreservesLE.le_iff (f := f)).mp h)
      (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ _ h hs := (Map.PreservesRxcSize.size_eq (f := f)).trans
    ((Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((Map.PreservesLE.le_iff (f := f)).mp h)
      (f.succ?_eq_some_iff.mp hs)).trans (congrArg Nat.succ (Map.PreservesRxcSize.size_eq (f := f)).symm))

public theorem Std.Rxc.IsAlwaysFinite.ofMap [LE α] [LE β] [Rxc.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLE] : Rxc.IsAlwaysFinite α where
  finite lo hi := by
    obtain ⟨n, hn⟩ := Rxc.IsAlwaysFinite.finite (f.toFun lo) (f.toFun hi)
    refine ⟨n, ?_⟩
    rw [f.succMany?_toFun] at hn
    cases hs : succMany? n lo with
    | none => exact True.intro
    | some b =>
      rw [hs] at hn
      exact fun h => hn ((Map.PreservesLE.le_iff (f := f)).mp h)

public theorem Std.PRange.LawfulUpwardEnumerableLT.ofMap [LT α] [LT β]
    [LawfulUpwardEnumerableLT β] (f : Map α β) [f.PreservesLT] :
    LawfulUpwardEnumerableLT α where
  lt_iff _ _ := (Map.PreservesLT.lt_iff (f := f)).trans
    ((LawfulUpwardEnumerableLT.lt_iff _ _).trans f.lt_iff.symm)

public theorem Std.Rxo.LawfulHasSize.ofMap [LT α] [LT β] [Rxo.HasSize α] [Rxo.HasSize β]
    [Rxo.LawfulHasSize β] (f : Map α β) [f.PreservesLT] [f.PreservesRxoSize] : Rxo.LawfulHasSize α where
  size_eq_zero_of_not_le _ _ h := (Map.PreservesRxoSize.size_eq (f := f)).trans
    (Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _ (fun h' => h ((Map.PreservesLT.lt_iff (f := f)).mpr h')))
  size_eq_one_of_succ?_eq_none _ _ h hs := (Map.PreservesRxoSize.size_eq (f := f)).trans
    (Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ ((Map.PreservesLT.lt_iff (f := f)).mp h)
      (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ _ h hs := (Map.PreservesRxoSize.size_eq (f := f)).trans
    ((Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ ((Map.PreservesLT.lt_iff (f := f)).mp h)
      (f.succ?_eq_some_iff.mp hs)).trans (congrArg Nat.succ (Map.PreservesRxoSize.size_eq (f := f)).symm))

public theorem Std.Rxo.IsAlwaysFinite.ofMap [LT α] [LT β] [Rxo.IsAlwaysFinite β] (f : Map α β)
    [f.PreservesLT] : Rxo.IsAlwaysFinite α where
  finite lo hi := by
    obtain ⟨n, hn⟩ := Rxo.IsAlwaysFinite.finite (f.toFun lo) (f.toFun hi)
    refine ⟨n, ?_⟩
    rw [f.succMany?_toFun] at hn
    cases hs : succMany? n lo with
    | none => exact True.intro
    | some b =>
      rw [hs] at hn
      exact fun h => hn ((Map.PreservesLT.lt_iff (f := f)).mp h)

public theorem Std.Rxi.LawfulHasSize.ofMap [Rxi.HasSize α] [Rxi.HasSize β] [Rxi.LawfulHasSize β]
    (f : Map α β) [f.PreservesRxiSize] : Rxi.LawfulHasSize α where
  size_eq_one_of_succ?_eq_none _ hs := (Map.PreservesRxiSize.size_eq (f := f)).trans
    (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ (f.succ?_eq_none_iff.mp hs))
  size_eq_succ_of_succ?_eq_some _ _ hs := (Map.PreservesRxiSize.size_eq (f := f)).trans
    ((Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ (f.succ?_eq_some_iff.mp hs)).trans
      (congrArg Nat.succ (Map.PreservesRxiSize.size_eq (f := f)).symm))

end RangeMap

end OmegaChecks.InitPort.Alternatives
