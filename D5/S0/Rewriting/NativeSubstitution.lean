/- GID: D5/S0/Rewriting/NativeSubstitution
   generality: G
   mirror-B: D5/B/S0/Rewriting/NativeSubstitution
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native constructor preservation under the original substitution operations. -/

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import D5.S0.Rewriting.NativeUnificationCore

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Strata.Util
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
abbrev HMaps (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  List (HMap α β)
namespace HMaps
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
def keys (ms : HMaps α β) : List α :=
  match ms with
  | [] => []
  | m :: rest => m.keys ++ keys rest
def values (ms : HMaps α β) : List β :=
  match ms with
  | [] => []
  | m :: rest => m.values ++ values rest
def push (ms : HMaps α β) (m : HMap α β) : HMaps α β :=
  m :: ms
def pop (ms : HMaps α β) : HMaps α β :=
  match ms with
  | [] => []
  | _ :: rest => rest
def newest (ms : HMaps α β) : HMap α β :=
  match ms with | [] => .empty | m :: _ => m
def find? [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) : Option β :=
  match ms with
  | [] => none
  | m :: rest =>
    match m.find? x with
    | none => find? rest x
    | some v => some v
def mapValues (f : β → γ) (ms : HMaps α β) : HMaps α γ :=
  ms.map (HMap.mapValues f)
def update [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) (v : β) : HMaps α β :=
  match ms with
  | [] => []
  | m :: rest =>
    match m.find? x with
    | none => m :: update rest x v
    | some _ => m.insert x v :: rest
def insert [EquivBEq α] [LawfulHashable α] (ms : HMaps α β) (x : α) (v : β) : HMaps α β :=
  match ms.find? x with
  | none => (ms.pop).push ((ms.newest).insert x v)
  | some _ => ms.update x v
theorem find?_mem_keys [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (h : ms.find? k = some v) : k ∈ ms.keys := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [find?] at h
    simp only [keys, List.mem_append]
    cases hm : m.find? k with
    | some w => exact Or.inl (HMap.find?_mem_keys m hm)
    | none => rw [hm] at h; exact Or.inr (ih h)
theorem find?_mem_values [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (h : ms.find? k = some v) : v ∈ ms.values := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [find?] at h
    simp only [values, List.mem_append]
    cases hm : m.find? k with
    | some w => rw [hm] at h; injection h with h; subst h; exact Or.inl (HMap.find?_mem_values m hm)
    | none => rw [hm] at h; exact Or.inr (ih h)
theorem find?_of_mem_keys [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (k : α) (hk : k ∈ ms.keys) : ∃ v, ms.find? k = some v := by
  induction ms with
  | nil => simp [keys] at hk
  | cons m rest ih =>
    simp only [keys, List.mem_append] at hk
    simp only [find?]
    cases hm : m.find? k with
    | some w => exact ⟨w, rfl⟩
    | none =>
      have h_not_m : k ∉ m.keys := HMap.find?_of_not_mem_keys m hm
      exact ih (hk.resolve_left h_not_m)
theorem not_mem_keys_find?_none [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (k : α) (h : k ∉ ms.keys) : ms.find? k = none := by
  cases hf : ms.find? k with
  | none => rfl
  | some v => exact absurd (find?_mem_keys ms hf) h
@[simp]
theorem mapValues_nil (f : β → γ) : mapValues f ([] : HMaps α β) = [] := by
  simp [mapValues]
@[simp]
theorem mapValues_cons (f : β → γ) (m : HMap α β) (rest : HMaps α β) :
    mapValues f (m :: rest) = m.mapValues f :: mapValues f rest := by
  simp [mapValues]
theorem find?_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (k : α) :
    (ms.mapValues f).find? k = (ms.find? k).map f := by
  induction ms with
  | nil => simp [find?]
  | cons m rest ih =>
    simp only [mapValues_cons, find?, HMap.find?_mapValues]
    cases hm : m.find? k with
    | some v => simp
    | none => simp only [Option.map_none]; exact ih
theorem mem_keys_mapValues_iff [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (k : α) :
    k ∈ (ms.mapValues f).keys ↔ k ∈ ms.keys := by
  induction ms with
  | nil => simp [keys]
  | cons m rest ih =>
    simp only [mapValues_cons, keys, List.mem_append]
    rw [HMap.mem_keys_mapValues_iff, ih]
theorem mem_values_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (ms : HMaps α β) (w : γ) :
    w ∈ (ms.mapValues f).values ↔ ∃ v, v ∈ ms.values ∧ w = f v := by
  induction ms with
  | nil => simp [values]
  | cons m rest ih =>
    simp only [mapValues_cons, values, List.mem_append]
    rw [HMap.mem_values_mapValues, ih]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨v, Or.inl hv, rfl⟩
      · exact ⟨v, Or.inr hv, rfl⟩
    · rintro ⟨v, hv | hv, rfl⟩
      · exact Or.inl ⟨v, hv, rfl⟩
      · exact Or.inr ⟨v, hv, rfl⟩
theorem find?_single_scope [EquivBEq α] [LawfulHashable α] (m : HMap α β) (x : α) :
    HMaps.find? [m] x = m.find? x := by
  simp only [find?]
  cases m.find? x <;> rfl
theorem find?_update_self [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) (h : ms.find? x ≠ none) :
    (ms.update x v).find? x = some v := by
  induction ms with
  | nil => simp [find?] at h
  | cons m rest ih =>
    simp only [update]; split
    · rename_i h_none; simp only [find?, h_none]; apply ih
      simp only [find?, h_none] at h; exact h
    · simp only [find?, HMap.find?_insert_self]
theorem find?_insert_self [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x : α) (v : β) :
    (ms.insert x v).find? x = some v := by
  simp only [insert]; split
  · rename_i h_none
    cases ms with
    | nil => simp only [pop, push, newest, find?, HMap.find?_insert_self]
    | cons m rest => simp only [pop, push, newest, find?, HMap.find?_insert_self]
  · exact find?_update_self ms x v (by simp_all)
theorem find?_insert_ne [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (x y : α) (v : β) (h_ne : x ≠ y) :
    (ms.insert y v).find? x = ms.find? x := by
  simp only [insert]
  cases h_fb : ms.find? y with
  | none =>
    cases ms with
    | nil =>
      simp only [pop, push, newest, find?]
      rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne]), HMap.find?_empty]
    | cons m rest =>
      simp only [pop, push, newest, find?]
      rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne])]
  | some val =>
    induction ms with
    | nil => simp [find?] at h_fb
    | cons m rest ih =>
      simp only [update]
      split
      · rename_i h_none
        simp only [find?]
        cases m.find? x with
        | none =>
          have h_rest : HMaps.find? rest y = some val := by
            simp only [find?, h_none] at h_fb; exact h_fb
          exact ih h_rest
        | some _ => rfl
      · simp only [find?]
        rw [HMap.find?_insert_ne _ y x v (by simp [bne, h_ne])]
private theorem update_keys_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ k, k ∈ (ms.update key val).keys → k ∈ ms.keys := by
  intro k hk
  induction ms with
  | nil => simp [update, keys] at hk
  | cons m rest ih =>
    simp only [update] at hk
    split at hk
    · simp only [keys, List.mem_append] at hk ⊢
      exact hk.imp id ih
    ·
      rename_i w h_find
      simp only [keys, List.mem_append] at hk ⊢
      rcases hk with h | h
      · left
        rcases List.mem_cons.mp (HMap.insert_keys_subset m key val k h) with h' | h'
        · rw [h']; exact HMap.find?_mem_keys m h_find
        · exact h'
      · right; exact h
private theorem update_values_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ v, v ∈ (ms.update key val).values → v ∈ val :: ms.values := by
  intro v hv
  induction ms with
  | nil => simp [update, values] at hv
  | cons m rest ih =>
    simp only [update] at hv
    split at hv
    · simp only [values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.mp (ih h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
    · simp only [values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · rcases List.mem_cons.mp (HMap.insert_values_subset m key val v h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
theorem insert_keys_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ k, k ∈ (ms.insert key val).keys → k ∈ key :: ms.keys := by
  intro k hk
  simp only [insert] at hk
  split at hk
  ·
    rename_i h_none
    cases ms with
    | nil =>
      simp only [pop, push, newest, keys, List.append_nil] at hk
      have := HMap.insert_keys_subset (.empty : HMap α β) key val k hk
      rcases List.mem_cons.mp this with h' | h'
      · rw [h']; exact List.mem_cons_self
      · obtain ⟨w, hw⟩ := (HMap.mem_keys_iff_find? .empty k).mp h'
        rw [HMap.find?_empty] at hw; exact absurd hw (by simp)
    | cons m rest =>
      simp only [pop, push, newest, keys, List.mem_append] at hk
      simp only [keys, List.mem_cons, List.mem_append]
      rcases hk with h | h
      · rcases List.mem_cons.mp (HMap.insert_keys_subset m key val k h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
  · exact List.mem_cons_of_mem _ (update_keys_subset ms key val k hk)
theorem insert_values_subset [LawfulBEq α] [LawfulHashable α]
    (ms : HMaps α β) (key : α) (val : β) :
    ∀ v, v ∈ (ms.insert key val).values → v ∈ val :: ms.values := by
  intro v hv
  simp only [insert] at hv
  split at hv
  · rename_i h_none
    cases ms with
    | nil =>
      simp only [pop, push, newest, values, List.append_nil] at hv
      have := HMap.insert_values_subset (.empty : HMap α β) key val v hv
      rcases List.mem_cons.mp this with h' | h'
      · rw [h']; exact List.mem_cons_self
      · obtain ⟨w, hw⟩ := (HMap.mem_values_iff_find? .empty v).mp h'
        rw [HMap.find?_empty] at hw; exact absurd hw (by simp)
    | cons m rest =>
      simp only [pop, push, newest, values, List.mem_append] at hv
      simp only [values, List.mem_cons, List.mem_append]
      rcases hv with h | h
      · rcases List.mem_cons.mp (HMap.insert_values_subset m key val v h) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
  · exact update_values_subset ms key val v hv
end HMaps
end
end Strata.Util

namespace Lambda
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
open Std (ToFormat Format format)
open Strata.Util (HMap HMaps)
set_option relaxedAutoImplicit true
abbrev SubstOne := HMap TyIdentifier LMonoTy
abbrev Subst := HMaps TyIdentifier LMonoTy
abbrev Subst.empty : Subst := []
def Subst.hasEmptyScopes (S : Subst) : Bool :=
  S.all (fun s => s.isEmpty)
def Subst.freeVars (S : Subst) : List TyIdentifier :=
  S.values.flatMap LMonoTy.freeVars
theorem Subst.freeVars_of_find_subset (S : Subst) (hi : HMaps.find? S i = some sty) :
    LMonoTy.freeVars sty ⊆ Subst.freeVars S := by
  have h_val := HMaps.find?_mem_values S hi
  simp only [Subst.freeVars]
  intro x hx
  exact List.mem_flatMap.mpr ⟨sty, h_val, hx⟩
def SubstWF (S : Subst) : Bool :=
  S.keys.all (fun k => k ∉ Subst.freeVars S)
@[simp]
theorem SubstWF_of_empty : SubstWF Subst.empty := by
  simp [SubstWF, HMaps.keys]
def Subst.singleton (tv : TyIdentifier) (ty : LMonoTy) : Subst :=
  [HMap.single tv ty]
theorem Subst.find?_singleton_self
    (tv : TyIdentifier) (ty : LMonoTy) :
    HMaps.find? (Subst.singleton tv ty) tv = some ty := by
  simp [Subst.singleton, HMaps.find?, HMap.find?_single_self]
theorem Subst.freeVars_singleton_subset
    (tv : TyIdentifier) (ty : LMonoTy) :
    Subst.freeVars (Subst.singleton tv ty) ⊆ ty.freeVars := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  have hv' : v ∈ (HMap.single tv ty).values := by
    simpa [Subst.singleton, HMaps.values] using hv
  rw [(HMap.mem_values_single_iff tv ty v).mp hv'] at hxv
  exact hxv
theorem Subst.freeVars_singleton_superset
    (tv : TyIdentifier) (ty : LMonoTy) :
    ty.freeVars ⊆ Subst.freeVars (Subst.singleton tv ty) := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap]
  refine ⟨ty, ?_, hx⟩
  simpa [Subst.singleton, HMaps.values] using (HMap.mem_values_single_iff tv ty ty).mpr rfl
theorem SubstWF.single_subst
    (tv : TyIdentifier) (ty : LMonoTy) (h : tv ∉ ty.freeVars) :
    SubstWF (Subst.singleton tv ty) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro k hk
  have hk_id : k = tv := by
    have : k ∈ (HMap.single tv ty).keys := by
      simpa [Subst.singleton, HMaps.keys] using hk
    exact (HMap.mem_keys_single_iff tv k ty).mp this
  rw [hk_id]
  exact fun hmem => h (Subst.freeVars_singleton_subset tv ty hmem)
structure SubstInfo where
  subst : Subst
  isWF : SubstWF subst
def SubstInfo.empty : SubstInfo :=
  { subst := Subst.empty,
    isWF := SubstWF_of_empty }
mutual
def LMonoTy.substCore (S : Subst) (mty : LMonoTy) : LMonoTy :=
  match mty with
  | .ftvar x => match S.find? x with
                | some sty => sty | none => mty
  | .bitvec n => .bitvec n
  | .tcons name ltys => .tcons name (LMonoTys.substCore S ltys)
def LMonoTys.substCore (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | ty :: rest => LMonoTy.substCore S ty :: LMonoTys.substCore S rest
end
def LMonoTy.subst (S : Subst) (mty : LMonoTy) : LMonoTy :=
  if Subst.hasEmptyScopes S then mty else LMonoTy.substCore S mty
def LMonoTys.subst (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  if Subst.hasEmptyScopes S then mtys else LMonoTys.substCore S mtys
theorem Subst.find?_none_of_hasEmptyScopes
    (h : Subst.hasEmptyScopes S) (x : TyIdentifier) : HMaps.find? S x = none := by
  induction S with
  | nil => rfl
  | cons m rest ih =>
    simp only [Subst.hasEmptyScopes, List.all_cons, Bool.and_eq_true] at h
    simp only [HMaps.find?, HMap.find?_of_isEmpty m x h.1]
    exact ih (by simp only [Subst.hasEmptyScopes]; exact h.2)
theorem LMonoTys.substCore_eq_map (S : Subst) (mtys : LMonoTys) :
    LMonoTys.substCore S mtys = mtys.map (LMonoTy.substCore S) := by
  induction mtys with
  | nil => rfl
  | cons hd tl ih => simp only [LMonoTys.substCore, List.map, ih]
theorem LMonoTy.subst_of_hasEmptyScopes
    (h : Subst.hasEmptyScopes S) (ty : LMonoTy) :
    LMonoTy.subst S ty = ty := by
  simp only [LMonoTy.subst, h, if_true]
theorem LMonoTy.subst_eq_substCore (S : Subst) (ty : LMonoTy)
    (h : Subst.hasEmptyScopes S = false) :
    LMonoTy.subst S ty = LMonoTy.substCore S ty := by
  simp only [LMonoTy.subst, h, Bool.false_eq_true, if_false]
theorem LMonoTy.subst_tcons (S : Subst) (name : String) (args : LMonoTys) :
    LMonoTy.subst S (.tcons name args) = .tcons name (LMonoTys.subst S args) := by
  simp only [LMonoTy.subst, LMonoTys.subst]
  split
  · rfl
  · simp only [LMonoTy.substCore]
theorem LMonoTy.subst_bitvec (S : Subst) (n : Nat) :
    LMonoTy.subst S (.bitvec n) = .bitvec n := by
  simp only [LMonoTy.subst]; split <;> rfl
theorem LMonoTys.subst_eq_map (S : Subst) (mtys : LMonoTys) :
    LMonoTys.subst S mtys = mtys.map (LMonoTy.subst S) := by
  simp only [LMonoTys.subst]
  split
  · rename_i h
    have h_map : mtys.map (LMonoTy.subst S) = mtys.map id :=
      List.map_congr_left (fun a _ => LMonoTy.subst_of_hasEmptyScopes h a)
    rw [h_map, List.map_id]
  · rename_i h
    have h' : Subst.hasEmptyScopes S = false := by
      simpa using h
    rw [LMonoTys.substCore_eq_map]
    exact List.map_congr_left (fun a _ => (LMonoTy.subst_eq_substCore S a h').symm)
theorem LMonoTy.subst_unfold (S : Subst) (ty : LMonoTy) :
    LMonoTy.subst S ty = match ty with
      | .ftvar x => match S.find? x with | some sty => sty | none => .ftvar x
      | .bitvec n => .bitvec n
      | .tcons name args => .tcons name (args.map (LMonoTy.subst S)) := by
  cases ty with
  | ftvar x =>
    by_cases h : Subst.hasEmptyScopes S
    · simp only [LMonoTy.subst_of_hasEmptyScopes h, Subst.find?_none_of_hasEmptyScopes h x]
    · simp only [Bool.not_eq_true] at h
      rw [LMonoTy.subst_eq_substCore S _ h, LMonoTy.substCore]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args => rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
theorem Subst.key_not_free_of_find
    (h : SubstWF S) (id : TyIdentifier) (hid : id ∈ S.keys) (x : TyIdentifier) :
    id ∉ LMonoTy.freeVars (LMonoTy.subst S (.ftvar x)) := by
  rw [LMonoTy.subst_unfold]
  cases hfind : S.find? x with
  | some sty =>
    simp only [hfind]
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h
    exact fun hmem => h id hid (Subst.freeVars_of_find_subset S hfind hmem)
  | none =>
    simp only [hfind, LMonoTy.freeVars, List.mem_singleton]
    intro h_id_eq; subst h_id_eq
    obtain ⟨v, hv⟩ := HMaps.find?_of_mem_keys S id hid
    rw [hv] at hfind; simp at hfind
mutual
theorem LMonoTy.subst_keys_not_in_substituted_type
    (h : SubstWF S) (ty : LMonoTy) :
    S.keys.all (fun k => k ∉ LMonoTy.freeVars (LMonoTy.subst S ty)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro id hid
  match ty with
  | .ftvar x => exact Subst.key_not_free_of_find h id hid x
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp [LMonoTy.freeVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons, LMonoTy.freeVars]
    have hlist := LMonoTys.subst_keys_not_in_substituted_type h args
    simp only [List.all_eq_true, decide_eq_true_eq] at hlist
    exact hlist id hid
theorem LMonoTys.subst_keys_not_in_substituted_type
    (h : SubstWF S) (mtys : LMonoTys) :
    S.keys.all (fun k => k ∉ LMonoTys.freeVars (LMonoTys.subst S mtys)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro id hid
  rw [LMonoTys.subst_eq_map]
  match mtys with
  | [] => simp [LMonoTys.freeVars]
  | ty :: rest =>
    simp only [List.map_cons, LMonoTys.freeVars, List.mem_append, not_or]
    have h_hd := LMonoTy.subst_keys_not_in_substituted_type h ty
    have h_tl := LMonoTys.subst_keys_not_in_substituted_type h rest
    rw [LMonoTys.subst_eq_map] at h_tl
    simp only [List.all_eq_true, decide_eq_true_eq] at h_hd h_tl
    exact ⟨h_hd id hid, h_tl id hid⟩
end
mutual
theorem LMonoTy.freeVars_of_subst_subset (S : Subst) (mty : LMonoTy) :
    LMonoTy.freeVars (LMonoTy.subst S mty) ⊆
    LMonoTy.freeVars mty ++ Subst.freeVars S := by
  match mty with
  | .ftvar x =>
    rw [LMonoTy.subst_unfold]
    cases hfind : S.find? x with
    | some sty =>
      simp only [hfind]
      intro v hv
      exact List.mem_append_right _ (Subst.freeVars_of_find_subset S hfind hv)
    | none => simp only [hfind, LMonoTy.freeVars]; intro v hv; exact List.mem_append_left _ hv
  | .bitvec n => rw [LMonoTy.subst_bitvec]; simp [LMonoTy.freeVars]
  | .tcons name args =>
    rw [LMonoTy.subst_tcons, LMonoTy.freeVars, LMonoTy.freeVars]
    exact LMonoTys.freeVars_of_subst_subset S args
theorem LMonoTys.freeVars_of_subst_subset (S : Subst) (mtys : LMonoTys) :
    LMonoTys.freeVars (LMonoTys.subst S mtys) ⊆
    LMonoTys.freeVars mtys ++ Subst.freeVars S := by
  rw [LMonoTys.subst_eq_map]
  match mtys with
  | [] => simp [LMonoTys.freeVars]
  | ty :: rest =>
    simp only [List.map_cons, LMonoTys.freeVars]
    have h_hd := LMonoTy.freeVars_of_subst_subset S ty
    have h_tl := LMonoTys.freeVars_of_subst_subset S rest
    rw [LMonoTys.subst_eq_map] at h_tl
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · rcases List.mem_append.mp (h_hd h) with h' | h'
      · exact List.mem_append_left _ (List.mem_append_left _ h')
      · exact List.mem_append_right _ h'
    · rcases List.mem_append.mp (h_tl h) with h' | h'
      · exact List.mem_append_left _ (List.mem_append_right _ h')
      · exact List.mem_append_right _ h'
end
def Subst.apply (new : SubstOne) (old : Subst) : Subst :=
  old.mapValues (LMonoTy.subst [new])
theorem Subst.mem_keys_apply_iff
    (new : SubstOne) (old : Subst) (k : TyIdentifier) :
    k ∈ (Subst.apply new old).keys ↔ k ∈ old.keys :=
  HMaps.mem_keys_mapValues_iff _ old k
theorem Subst.find?_apply
    (new : SubstOne) (S : Subst) (x : TyIdentifier) :
    HMaps.find? (Subst.apply new S) x = (HMaps.find? S x).map (LMonoTy.subst [new]) :=
  HMaps.find?_mapValues _ S x
theorem Subst.keys_not_in_apply
    (newS : SubstOne) (oldS : Subst) (h : SubstWF [newS]) :
    (HMaps.keys [newS]).all (fun k => k ∉ Subst.freeVars (Subst.apply newS oldS)) := by
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro k hk hmem
  simp only [Subst.freeVars, List.mem_flatMap] at hmem
  obtain ⟨mty, h_mty, h_fv⟩ := hmem
  rw [Subst.apply, HMaps.mem_values_mapValues] at h_mty
  obtain ⟨v, _hv, rfl⟩ := h_mty
  have h_keys := LMonoTy.subst_keys_not_in_substituted_type h v
  simp only [List.all_eq_true, decide_eq_true_eq] at h_keys
  exact h_keys k hk h_fv
theorem Subst.freeVars_of_apply_subset
    (new : SubstOne) (S : Subst) (mty : LMonoTy)
    (h : mty ∈ HMaps.values (Subst.apply new S)) :
    LMonoTy.freeVars mty ⊆ Subst.freeVars [new] ++ Subst.freeVars S := by
  rw [Subst.apply, HMaps.mem_values_mapValues] at h
  obtain ⟨v, hv, rfl⟩ := h
  have h_sub := LMonoTy.freeVars_of_subst_subset [new] v
  intro x hx
  rcases List.mem_append.mp (h_sub hx) with h1 | h1
  · refine List.mem_append_right _ ?_
    simp only [Subst.freeVars]
    exact List.mem_flatMap.mpr ⟨v, hv, h1⟩
  · exact List.mem_append_left _ h1
theorem Subst.freeVars_of_apply_subset_alt
    (new : SubstOne) (S : Subst) :
    Subst.freeVars (Subst.apply new S) ⊆
    Subst.freeVars [new] ++ Subst.freeVars S := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨mty, h_mty, h_fv⟩ := hx
  exact Subst.freeVars_of_apply_subset new S mty h_mty h_fv
theorem SubstWF.apply_one_substituted_type
    (S : Subst) (hS : SubstWF S) (id : TyIdentifier) (ty : LMonoTy) :
    SubstWF (Subst.apply (HMap.single id (LMonoTy.subst S ty)) S) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro k hk hmem
  have hk_S : k ∈ S.keys := (Subst.mem_keys_apply_iff _ S k).mp hk
  have h_sub := Subst.freeVars_of_apply_subset_alt (HMap.single id (LMonoTy.subst S ty)) S hmem
  rcases List.mem_append.mp h_sub with h1 | h1
  ·
    have h_single := Subst.freeVars_singleton_subset id (LMonoTy.subst S ty)
    simp only [Subst.singleton] at h_single
    have h_key := LMonoTy.subst_keys_not_in_substituted_type hS ty
    simp only [List.all_eq_true, decide_eq_true_eq] at h_key
    exact h_key k hk_S (h_single h1)
  ·
    simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at hS
    exact hS k hk_S h1
theorem Subst.freeVars_of_insert
    (S : Subst) (id : TyIdentifier) (ty : LMonoTy) :
    Subst.freeVars (HMaps.insert S id ty) ⊆ Subst.freeVars S ++ LMonoTy.freeVars ty := by
  intro x hx
  simp only [Subst.freeVars, List.mem_flatMap] at hx
  obtain ⟨v, hv, hxv⟩ := hx
  have h_val := HMaps.insert_values_subset S id ty v hv
  rcases List.mem_cons.mp h_val with h1 | h1
  · subst h1; exact List.mem_append_right _ hxv
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, h1, hxv⟩)
theorem SubstWF_mk_insert
    (S : Subst) (i : TyIdentifier) (ty : LMonoTy)
    (h_i_not_in_S_values : i ∉ Subst.freeVars S)
    (h_keys_not_in_ty : S.keys.all (fun k => k ∉ ty.freeVars))
    (h_s_WF : SubstWF (Subst.singleton i ty))
    (h_S_WF : SubstWF S) :
    SubstWF (HMaps.insert S i ty) := by
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq]
  intro x hx_keys hx_fv
  have h_keys := HMaps.insert_keys_subset S i ty x hx_keys
  have h_fv := Subst.freeVars_of_insert S i ty hx_fv
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_S_WF
  simp only [List.all_eq_true, decide_eq_true_eq] at h_keys_not_in_ty
  rcases List.mem_cons.mp h_keys with hx_i | hx_S
  · rw [hx_i] at h_fv
    rcases List.mem_append.mp h_fv with h | h
    · exact h_i_not_in_S_values h
    · simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_s_WF
      exact h_s_WF i (by simp [Subst.singleton, HMaps.keys, HMap.mem_keys_single_iff])
        (Subst.freeVars_singleton_superset i ty h)
  · rcases List.mem_append.mp h_fv with h | h
    · exact h_S_WF x hx_S h
    · exact h_keys_not_in_ty x hx_S h
theorem SubstWF.cons_of_subst_apply
    (S : Subst) (hS : SubstWF S) (id : TyIdentifier) (ty newty : LMonoTy)
    (h_newty : newty = LMonoTy.subst S ty)
    (h_id_not_in_newty : id ∉ newty.freeVars) :
    SubstWF (HMaps.insert (Subst.apply (HMap.single id newty) S) id newty) := by
  have h_apply_WF : SubstWF (Subst.apply (HMap.single id newty) S) := by
    rw [h_newty]; exact SubstWF.apply_one_substituted_type S hS id ty
  have h_id_not_free : id ∉ Subst.freeVars (Subst.apply (HMap.single id newty) S) := by
    have := Subst.keys_not_in_apply (HMap.single id newty) S
      (SubstWF.single_subst id newty h_id_not_in_newty)
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this id (by simp [HMaps.keys, HMap.mem_keys_single_iff])
  have h_keys_not_in_newty :
      (Subst.apply (HMap.single id newty) S).keys.all (fun k => k ∉ newty.freeVars) := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro k hk
    have hk_S : k ∈ S.keys := (Subst.mem_keys_apply_iff _ S k).mp hk
    rw [h_newty]
    have h_key := LMonoTy.subst_keys_not_in_substituted_type hS ty
    simp only [List.all_eq_true, decide_eq_true_eq] at h_key
    exact h_key k hk_S
  exact SubstWF_mk_insert (Subst.apply (HMap.single id newty) S) id newty
    h_id_not_free h_keys_not_in_newty
    (SubstWF.single_subst id newty h_id_not_in_newty) h_apply_WF
theorem LMonoTy.subst_no_relevant_keys (S : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ HMaps.keys S) :
    LMonoTy.subst S mty = mty := by
  induction mty with
  | ftvar x =>
    rw [LMonoTy.subst_unfold]
    simp only [HMaps.not_mem_keys_find?_none S x (h x (by simp [LMonoTy.freeVars]))]
  | bitvec n => rw [LMonoTy.subst_bitvec]
  | tcons name args ih =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map]
    congr 1
    have h_map : args.map (LMonoTy.subst S) = args.map id :=
      List.map_congr_left (fun a ha => ih a ha (fun x hx =>
        h x (by simp only [LMonoTy.freeVars]; exact LMonoTys.freeVars_mem_subset ha hx)))
    rw [h_map, List.map_id]
theorem LMonoTy.subst_idempotent_value
    (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : HMaps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S t = t := by
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_x_in_fvs : x ∈ Subst.freeVars S := Subst.freeVars_of_find_subset S h_find hx
  simp only [SubstWF, List.all_eq_true, decide_eq_true_eq] at h_wf
  intro h_x_key
  exact h_wf x h_x_key h_x_in_fvs
theorem LMonoTy.subst_no_key_free (S : Subst) (ty : LMonoTy)
    (h : S.keys.all (fun k => k ∉ ty.freeVars)) :
    LMonoTy.subst S ty = ty := by
  apply LMonoTy.subst_no_relevant_keys
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact fun x hx h_key => h x h_key hx
theorem LMonoTy.subst_idempotent
    (S : Subst) (hWF : SubstWF S) (ty : LMonoTy) :
    LMonoTy.subst S (LMonoTy.subst S ty) = LMonoTy.subst S ty :=
  LMonoTy.subst_no_key_free S (LMonoTy.subst S ty)
    (LMonoTy.subst_keys_not_in_substituted_type hWF ty)
end
end Lambda

namespace NativeTermUnification
open Lambda Strata.Util
def NativeSubst (S : Subst) : Prop := ∀ t ∈ S.values, Shape t
theorem shape_subst (S : Subst) (hS : NativeSubst S) (t : LMonoTy) (ht : Shape t) :
    Shape (LMonoTy.subst S t) := by
  induction ht with
  | var s =>
    rw [LMonoTy.subst_unfold]
    cases h : S.find? s with
    | none => simpa only [h] using Shape.var s
    | some t => simpa only [h] using hS t (HMaps.find?_mem_values S h)
  | bool b =>
    cases b
    · simpa [leaf, LMonoTy.subst_tcons, LMonoTys.subst_eq_map] using Shape.bool false
    · simpa [leaf, LMonoTy.subst_tcons, LMonoTys.subst_eq_map] using Shape.bool true
  | mul ha hb iha ihb =>
    simpa [pair, LMonoTy.subst_tcons, LMonoTys.subst_eq_map] using Shape.mul iha ihb
theorem native_insert (S : Subst) (s : String) (t : LMonoTy)
    (hS : NativeSubst S) (ht : Shape t) : NativeSubst (S.insert s t) := by
  intro v hv
  rcases List.mem_cons.mp (HMaps.insert_values_subset S s t v hv) with h | h
  · simpa [h] using ht
  · exact hS v h
theorem native_apply (S : Subst) (s : String) (t : LMonoTy)
    (hS : NativeSubst S) (ht : Shape t) : NativeSubst (Subst.apply (HMap.single s t) S) := by
  intro v hv
  rw [Subst.apply, HMaps.mem_values_mapValues] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  apply shape_subst _ _ _ (hS a ha)
  intro b hb
  have : b ∈ (HMap.single s t).values := by simpa [HMaps.values] using hb
  have := (HMap.mem_values_single_iff s t b).mp this
  simpa [this] using ht
end NativeTermUnification
namespace NativeTermUnification
open Lambda Strata.Util
theorem shape_children {nm : String} {args : LMonoTys} (h : Shape (.tcons nm args)) :
    ∀ t ∈ args, Shape t := by
  cases h with
  | bool b => cases b <;> simp [leaf] at *
  | mul ha hb => intro t ht; simp at ht
                 rcases ht with rfl | rfl <;> assumption
end NativeTermUnification
