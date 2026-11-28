/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Data.List.Basic
public import OmegaInit.Control.Id
public import OmegaInit.GetElem
public import OmegaInit.WF
import OmegaInit.Data.Nat.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

theorem ext' {α : Type u} {xs ys : Array α} (h : Eq (Array.toList xs) (Array.toList ys)) :
    Eq xs ys := congrArg Array.mk h

theorem size_push {α : Type u} {xs : Array α} (v : α) :
    Eq (Array.size (Array.push xs v)) (Nat.add (Array.size xs) (Nat.succ Nat.zero)) :=
  List.length_concat.trans (Nat.add_one (Array.size xs)).symm

@[no_expose] def eraseIdxIfInBounds {α : Type u} (xs : Array α) (i : Nat) : Array α :=
  Array.mk (List.eraseIdx (Array.toList xs) i)

attribute [irreducible] Array.eraseIdxIfInBounds

end Omega.Array

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

port_proof Array.isEqv._proof_1
port_definition Array.foldlM.loop.match_1
port_definition Array.foldlM.loop._f
port_definition Array.foldlM.loop
port_definition Array.foldlM
port_definition Array.foldl
port_definition Array.append
port_proof Array.mapM.map._unary._proof_1
port_definition Array.mapM.map._unary
port_definition Array.mapM.map
port_definition Array.mapM
port_definition Array.map
port_definition Array.instAppend

public theorem Omega.Array.foldlM.loop._proof_1 {α : Type u} (as : Omega.Array α) (stop : Omega.Nat)
    (h : Omega.Nat.le stop (Omega.Array.size as)) (j : Omega.Nat) (hlt : Omega.Nat.lt j stop) :
    Omega.Nat.lt j (Omega.Array.size as) := Omega.Nat.lt_of_lt_of_le hlt h
