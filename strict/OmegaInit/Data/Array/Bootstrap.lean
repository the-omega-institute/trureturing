/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Array.Basic
import all OmegaInit.Data.Array.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

attribute [local semireducible] Array.append

theorem toList_push {α : Type u} {xs : Array α} {x : α} :
    Eq (Array.toList (Array.push xs x)) (List.append (Array.toList xs) (List.cons x List.nil)) :=
  List.concat_eq_append

theorem toList_append {α : Type u} {xs ys : Array α} :
    Eq (Array.toList (Array.append xs ys)) (List.append (Array.toList xs) (Array.toList ys)) :=
  Omega.rfl

theorem append_empty {α : Type u} {xs : Array α} : Eq (Array.append xs Array.empty) xs :=
  ext' (List.append_nil (Array.toList xs))

theorem empty_append {α : Type u} {xs : Array α} : Eq (Array.append Array.empty xs) xs :=
  Omega.rfl

theorem append_assoc {α : Type u} {xs ys zs : Array α} :
    Eq (Array.append (Array.append xs ys) zs) (Array.append xs (Array.append ys zs)) :=
  ext' (List.append_assoc (Array.toList xs) (Array.toList ys) (Array.toList zs))

end Omega.Array

port_proof Array.append_eq_append by_reflexivity
port_proof Array.toList_empty by_reflexivity
