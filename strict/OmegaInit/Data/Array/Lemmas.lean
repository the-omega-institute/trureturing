/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
module
prelude
public import OmegaInit.Data.Array.Basic
public import OmegaInit.Core
import OmegaInit.Data.Array.Bootstrap
import OmegaInit.Data.List.Lemmas
import all OmegaInit.Data.Array.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

attribute [local semireducible] Array.append Array.map Array.eraseIdxIfInBounds

theorem toList_inj {α : Type u} {xs ys : Array α} :
    Iff (Eq (Array.toList xs) (Array.toList ys)) (Eq xs ys) :=
  Iff.intro ext' (congrArg Array.toList)

theorem toList_eq_nil_iff {α : Type u} {xs : Array α} :
    Iff (Eq (Array.toList xs) List.nil) (Eq xs Array.empty) :=
  toList_inj

set_option relaxedAutoImplicit true in
theorem eq_empty_of_size_eq_zero (h : Eq (Array.size xs) Nat.zero) :
    Eq xs Array.empty := ext' (List.eq_nil_of_length_eq_zero h)

set_option relaxedAutoImplicit true in
theorem size_eq_zero_iff : Iff (Eq (Array.size xs) Nat.zero) (Eq xs Array.empty) :=
  Iff.intro eq_empty_of_size_eq_zero (congrArg Array.size)

set_option relaxedAutoImplicit true in
theorem eq_empty_iff_size_eq_zero : Iff (Eq xs Array.empty) (Eq (Array.size xs) Nat.zero) :=
  size_eq_zero_iff.symm

theorem toList_eraseIdxIfInBounds {α : Type u} {xs : Array α} {i : Nat} :
    Eq (Array.toList (Array.eraseIdxIfInBounds xs i)) (List.eraseIdx (Array.toList xs) i) := Omega.rfl

theorem size_map {α : Type u} {β : Type v} {f : α → β} {xs : Array α} :
    Eq (Array.size (Array.map f xs)) (Array.size xs) := List.length_map f

theorem map_push {α : Type u} {β : Type v} {f : α → β} {as : Array α} {x : α} :
    Eq (Array.map f (Array.push as x)) (Array.push (Array.map f as) (f x)) :=
  ext' List.map_concat

theorem map_id {α : Type u} (xs : Array α) : Eq (Array.map id xs) xs := ext' (List.map_id _)

theorem map_id'' {α : Type u} {f : α → α} (h : ∀ x, Eq (f x) x) (xs : Array α) :
    Eq (Array.map f xs) xs := ext' (List.map_id'' h _)

theorem map_eq_empty_iff {α : Type u} {β : Type v} {f : α → β} {xs : Array α} :
    Iff (Eq (Array.map f xs) Array.empty) (Eq xs Array.empty) :=
  Iff.intro (fun h => eq_empty_of_size_eq_zero (size_map.symm.trans (congrArg Array.size h)))
    (congrArg (Array.map f))

theorem eq_empty_of_map_eq_empty {α : Type u} {β : Type v} {f : α → β} {xs : Array α}
    (h : Eq (Array.map f xs) Array.empty) : Eq xs Array.empty := map_eq_empty_iff.mp h

theorem map_map {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {as : Array α} :
    Eq (Array.map g (Array.map f as)) (Array.map (fun x => g (f x)) as) := ext' List.map_map

private theorem mapSection {α : Type u} {β : Type v} (pack : α → β) (unpack : β → α)
    (h : ∀ x, Eq (pack (unpack x)) x) (xs : List β) :
    Eq (List.map pack (List.map unpack xs)) xs := List.map_map.trans (List.map_id'' h xs)

theorem array₂_induction {α : Type u} (P : Array (Array α) → Prop)
    (of : ∀ (xss : List (List α)), P (List.toArray (List.map List.toArray xss)))
    (xss : Array (Array α)) : P xss :=
  let roundtrip := mapSection List.toArray Array.toList (fun _ => Omega.rfl) (Array.toList xss)
  Eq.subst (motive := P) (congrArg List.toArray roundtrip) (of (List.map Array.toList (Array.toList xss)))

theorem array₃_induction {α : Type u} (P : Array (Array (Array α)) → Prop)
    (of : ∀ (xss : List (List (List α))),
      P (List.toArray (List.map List.toArray (List.map (List.map List.toArray) xss))))
    (xss : Array (Array (Array α))) : P xss :=
  array₂_induction P (fun lists =>
    let roundtrip := mapSection (List.map List.toArray) (List.map Array.toList)
      (mapSection List.toArray Array.toList (fun _ => Omega.rfl)) lists
    Eq.subst (motive := fun ys => P (List.toArray (List.map List.toArray ys))) roundtrip
      (of (List.map (List.map Array.toList) lists))) xss

theorem size_append {α : Type u} {xs ys : Array α} :
    Eq (Array.size (Array.append xs ys)) (Nat.add (Array.size xs) (Array.size ys)) :=
  List.length_append

theorem map_append {α : Type u} {β : Type v} {f : α → β} {xs ys : Array α} :
    Eq (Array.map f (Array.append xs ys)) (Array.append (Array.map f xs) (Array.map f ys)) :=
  ext' List.map_append

theorem toArray_eq_append_iff {α : Type u} {xs : List α} {as bs : Array α} :
    Iff (Eq (List.toArray xs) (Array.append as bs)) (Eq xs (List.append (Array.toList as) (Array.toList bs))) :=
  Iff.intro (congrArg Array.toList) ext'

theorem append_eq_toArray_iff {α : Type u} {xs ys : Array α} {as : List α} :
    Iff (Eq (Array.append xs ys) (List.toArray as)) (Eq (List.append (Array.toList xs) (Array.toList ys)) as) :=
  Iff.intro (congrArg Array.toList) ext'

theorem append_eq_empty_iff {α : Type u} {xs ys : Array α} :
    Iff (Eq (Array.append xs ys) Array.empty) (And (Eq xs Array.empty) (Eq ys Array.empty)) :=
  Iff.intro (fun e =>
    let h := List.append_eq_nil_iff.mp (congrArg Array.toList e)
    And.intro (ext' h.left) (ext' h.right))
    (fun h => ext' (List.append_eq_nil_iff.mpr (And.intro (congrArg Array.toList h.left)
      (congrArg Array.toList h.right))))

theorem empty_eq_append_iff {α : Type u} {xs ys : Array α} :
    Iff (Eq Array.empty (Array.append xs ys)) (And (Eq xs Array.empty) (Eq ys Array.empty)) :=
  Iff.intro (fun h => append_eq_empty_iff.mp h.symm) (fun h => (append_eq_empty_iff.mpr h).symm)

end Omega.Array

port_proof Array.length_toList by_reflexivity
port_proof Array.toList_map by_reflexivity
port_proof List.map_toArray by_reflexivity
port_proof Array.map_empty by_reflexivity
port_proof Array.map_singleton by_reflexivity
port_proof Array.singleton_eq_toArray_singleton by_reflexivity
port_proof Array.map_id' using Omega.Array.map_id

port_proof Option.getD.eq_1 by_reflexivity
port_proof Option.getD.eq_2 by_reflexivity
