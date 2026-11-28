/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Array.Basic
import OmegaInit.Data.List.Lemmas
import OmegaInit.SimpLemmas
import OmegaInit.Data.Nat.Basic

noncomputable section

@[expose] public section

namespace Omega.Array

theorem toList_push {α : Type u} {xs : Array α} {x : α} :
    Eq (Array.toList (Array.push xs x)) (List.append (Array.toList xs) (List.cons x List.nil)) :=
  List.concat_eq_append

end Omega.Array

port_proof Array.toList_empty by_reflexivity

port_proof Array.append_eq_append
port_proof Array.foldlM.loop.eq_def
port_alternative_proof Array.foldl_toList from OmegaChecks.InitPort.Alternatives.Array
port_alternative_proof Array.toList_append from OmegaChecks.InitPort.Alternatives.Array

namespace Omega.Array

public theorem append_empty {α : Type u} {xs : Array α} : Eq (Array.append xs Array.empty) xs :=
  ext' (toList_append.trans (List.append_nil xs.toList))

public theorem empty_append {α : Type u} {xs : Array α} : Eq (Array.append Array.empty xs) xs :=
  ext' toList_append

public theorem append_assoc {α : Type u} {xs ys zs : Array α} :
    Eq (Array.append (Array.append xs ys) zs) (Array.append xs (Array.append ys zs)) :=
  ext' (toList_append.trans ((congrArg (fun l => List.append l zs.toList) toList_append).trans
    ((List.append_assoc xs.toList ys.toList zs.toList).trans
      ((congrArg (List.append xs.toList) toList_append.symm).trans toList_append.symm))))

end Omega.Array
