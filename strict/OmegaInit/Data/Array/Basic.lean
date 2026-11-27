/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Data.List.Basic
import OmegaInit.Data.Nat.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

theorem ext' {α : Type u} {xs ys : Array α} (h : Eq (Array.toList xs) (Array.toList ys)) :
    Eq xs ys := congrArg Array.mk h

theorem size_push {α : Type u} {xs : Array α} (v : α) :
    Eq (Array.size (Array.push xs v)) (Nat.add (Array.size xs) (Nat.succ Nat.zero)) :=
  List.length_concat.trans (Nat.add_one (Array.size xs)).symm

@[no_expose] protected def append {α : Type u} (as bs : Array α) : Array α :=
  Array.mk (List.append (Array.toList as) (Array.toList bs))

@[no_expose] def map {α : Type u} {β : Type v} (f : α → β) (as : Array α) : Array β :=
  Array.mk (List.map f (Array.toList as))

@[no_expose] def eraseIdxIfInBounds {α : Type u} (xs : Array α) (i : Nat) : Array α :=
  Array.mk (List.eraseIdx (Array.toList xs) i)

attribute [irreducible] Array.append Array.map Array.eraseIdxIfInBounds

end Omega.Array

port_definition Array.instAppend
port_proof Array.toArray_toList by_reflexivity
port_proof Array.emptyWithCapacity_eq by_reflexivity
port_proof Array.mkEmpty_eq by_reflexivity
port_proof List.toList_toArray by_reflexivity
port_proof List.size_toArray by_reflexivity
port_proof Array.size_eq_length_toList by_reflexivity
port_definition Array.markLinear
port_proof Array.markLinear_eq by_reflexivity
port_definition Array.propagateMark
attribute [never_extract] Omega.Array.markLinear Omega.Array.propagateMark
port_proof Array.propagateMark_eq by_reflexivity
