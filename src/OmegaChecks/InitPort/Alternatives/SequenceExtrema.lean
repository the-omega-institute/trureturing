module
public import Init.Data.Array.MinMax

/-! Membership and extremal bounds for extrema of lists and arrays. -/
namespace OmegaChecks.InitPort.Alternatives

open Std

public theorem List.min?_eq_some_iff : type_of% @_root_.List.min?_eq_some_iff := by
  intro α a inst le xs order laws
  letI : MinEqOr α := laws.toMinEqOr
  letI : LawfulOrderInf α := laws.toLawfulOrderInf
  constructor
  · intro h
    exact ⟨_root_.List.min?_mem h, (_root_.List.le_min?_iff h).1 (Std.le_refl _)⟩
  · rintro ⟨ha, bound⟩
    cases xs with
    | nil => cases ha
    | cons x xs =>
      apply congrArg some
      have first := (_root_.List.le_min?_iff (xs := x :: xs) rfl).1 (Std.le_refl _) _ ha
      have second := bound _ (_root_.List.min?_mem (xs := x :: xs) rfl)
      exact Std.le_antisymm first second

public theorem List.min_eq_iff : type_of% @_root_.List.min_eq_iff := by
  intro α a inst le xs order laws h
  have someEq := _root_.List.min?_eq_some_min h
  exact ⟨fun e => List.min?_eq_some_iff.mp (someEq.trans (congrArg some e)),
    fun c => Option.some.inj (someEq.symm.trans (List.min?_eq_some_iff.mpr c))⟩

public theorem List.min_replicate : type_of% @_root_.List.min_replicate := by
  intro α inst idem n a h
  have pos : 0 < n := Nat.pos_of_ne_zero (fun e => h (by subst n; rfl))
  exact Option.some.inj ((_root_.List.min?_eq_some_min h).symm.trans
    (_root_.List.min?_replicate_of_pos pos))

public theorem Array.min?_eq_some_iff : type_of% @_root_.Array.min?_eq_some_iff := by
  intro α a inst le xs order laws
  cases xs with
  | mk l =>
    rw [_root_.List.min?_toArray]
    constructor
    · intro h
      obtain ⟨ha, bound⟩ := List.min?_eq_some_iff.mp h
      exact ⟨List.mem_toArray.mpr ha, fun b hb => bound b (List.mem_toArray.mp hb)⟩
    · rintro ⟨ha, bound⟩
      exact List.min?_eq_some_iff.mpr ⟨List.mem_toArray.mp ha,
        fun b hb => bound b (List.mem_toArray.mpr hb)⟩

public theorem Array.min_eq_iff : type_of% @_root_.Array.min_eq_iff := by
  intro α a inst le xs order laws h
  have someEq := _root_.Array.min?_eq_some_min h
  exact ⟨fun e => Array.min?_eq_some_iff.mp (someEq.trans (congrArg some e)),
    fun c => Option.some.inj (someEq.symm.trans (Array.min?_eq_some_iff.mpr c))⟩

public theorem List.max?_eq_some_iff : type_of% @_root_.List.max?_eq_some_iff := by
  intro α a inst le xs order laws
  letI : MaxEqOr α := laws.toMaxEqOr
  letI : LawfulOrderSup α := laws.toLawfulOrderSup
  constructor
  · intro h
    exact ⟨_root_.List.max?_mem h, (_root_.List.max?_le_iff h).1 (Std.le_refl _)⟩
  · rintro ⟨ha, bound⟩
    cases xs with
    | nil => cases ha
    | cons x xs =>
      apply congrArg some
      have first := (_root_.List.max?_le_iff (xs := x :: xs) rfl).1 (Std.le_refl _) _ ha
      have second := bound _ (_root_.List.max?_mem (xs := x :: xs) rfl)
      exact Std.le_antisymm second first

public theorem List.max_eq_iff : type_of% @_root_.List.max_eq_iff := by
  intro α a inst le xs order laws h
  have someEq := _root_.List.max?_eq_some_max h
  exact ⟨fun e => List.max?_eq_some_iff.mp (someEq.trans (congrArg some e)),
    fun c => Option.some.inj (someEq.symm.trans (List.max?_eq_some_iff.mpr c))⟩

public theorem List.max_replicate : type_of% @_root_.List.max_replicate := by
  intro α inst idem n a h
  have pos : 0 < n := Nat.pos_of_ne_zero (fun e => h (by subst n; rfl))
  exact Option.some.inj ((_root_.List.max?_eq_some_max h).symm.trans
    (_root_.List.max?_replicate_of_pos pos))

public theorem Array.max?_eq_some_iff : type_of% @_root_.Array.max?_eq_some_iff := by
  intro α a inst le xs order laws
  cases xs with
  | mk l =>
    rw [_root_.List.max?_toArray]
    constructor
    · intro h
      obtain ⟨ha, bound⟩ := List.max?_eq_some_iff.mp h
      exact ⟨List.mem_toArray.mpr ha, fun b hb => bound b (List.mem_toArray.mp hb)⟩
    · rintro ⟨ha, bound⟩
      exact List.max?_eq_some_iff.mpr ⟨List.mem_toArray.mp ha,
        fun b hb => bound b (List.mem_toArray.mpr hb)⟩

public theorem Array.max_eq_iff : type_of% @_root_.Array.max_eq_iff := by
  intro α a inst le xs order laws h
  have someEq := _root_.Array.max?_eq_some_max h
  exact ⟨fun e => Array.max?_eq_some_iff.mp (someEq.trans (congrArg some e)),
    fun c => Option.some.inj (someEq.symm.trans (Array.max?_eq_some_iff.mpr c))⟩


public theorem List.min?_eq_some_iff_subtype : type_of% @_root_.List.min?_eq_some_iff_subtype := by
  intro α a inst le xs sel order laws
  rw [_root_.List.min?_eq_min?_attach, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨v, hv⟩, present, rfl⟩
    obtain ⟨_, bound⟩ := List.min?_eq_some_iff.mp present
    exact ⟨hv, fun b hb => bound ⟨b, hb⟩ (List.mem_attach _ _)⟩
  · rintro ⟨ha, bound⟩
    refine ⟨⟨a, ha⟩, List.min?_eq_some_iff.mpr ⟨List.mem_attach _ _, ?_⟩, rfl⟩
    exact fun b _ => bound b.val b.property

public theorem List.max?_eq_some_iff_subtype : type_of% @_root_.List.max?_eq_some_iff_subtype := by
  intro α a inst le xs sel order laws
  rw [_root_.List.max?_eq_max?_attach, Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨v, hv⟩, present, rfl⟩
    obtain ⟨_, bound⟩ := List.max?_eq_some_iff.mp present
    exact ⟨hv, fun b hb => bound ⟨b, hb⟩ (List.mem_attach _ _)⟩
  · rintro ⟨ha, bound⟩
    refine ⟨⟨a, ha⟩, List.max?_eq_some_iff.mpr ⟨List.mem_attach _ _, ?_⟩, rfl⟩
    exact fun b _ => bound b.val b.property

end OmegaChecks.InitPort.Alternatives
