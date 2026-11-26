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

attribute [local semireducible] Array.append Array.map

theorem toList_inj {α : Type u} {xs ys : Array α} :
    Iff (Eq (Array.toList xs) (Array.toList ys)) (Eq xs ys) :=
  Iff.intro ext' (congrArg Array.toList)

theorem toList_eq_nil_iff {α : Type u} {xs : Array α} :
    Iff (Eq (Array.toList xs) List.nil) (Eq xs Array.empty) :=
  toList_inj

set_option relaxedAutoImplicit true in
theorem eq_empty_of_size_eq_zero (h : Eq (Array.size xs) Nat.zero) :
    Eq xs Array.empty := ext' (List.eq_nil_of_length_eq_zero h)

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

theorem map_map {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {as : Array α} :
    Eq (Array.map g (Array.map f as)) (Array.map (fun x => g (f x)) as) := ext' List.map_map

theorem size_append {α : Type u} {xs ys : Array α} :
    Eq (Array.size (Array.append xs ys)) (Nat.add (Array.size xs) (Array.size ys)) :=
  List.length_append

theorem map_append {α : Type u} {β : Type v} {f : α → β} {xs ys : Array α} :
    Eq (Array.map f (Array.append xs ys)) (Array.append (Array.map f xs) (Array.map f ys)) :=
  ext' List.map_append

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
