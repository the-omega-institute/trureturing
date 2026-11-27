/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module
prelude
public import OmegaInit.Core
public import OmegaInit.Data.Option.Basic
import all OmegaInit.Data.Option.Basic
import OmegaInit.PropLemmas

namespace Omega.Option

theorem all_false {α : Type u} {o : Option α} : Eq (Option.all (fun _ => Bool.false) o) (Option.isNone o) :=
  Option.casesOn (motive := fun x => Eq (Option.all (fun _ => Bool.false) x) (Option.isNone x))
    o Option.isNone_none.symm (fun a => (Option.isNone_some (a := a)).symm)

end Omega.Option
port_proof Option.all_map
port_proof Option.merge_none_right
port_proof Option.any_map
port_proof Option.any_true by_reflexivity
port_proof Option.bind_assoc
port_proof Option.bind_comm
port_proof Option.bind_fun_none
port_proof Option.bind_fun_some
port_proof Option.bind_id_eq_join by_reflexivity
port_proof Option.elim_none by_reflexivity
port_proof Option.elim_some by_reflexivity
port_proof Option.exists
port_proof Option.eq_none_or_eq_some
port_proof Option.ext
port_proof Option.ext_iff
port_proof Option.forall
port_proof Option.getD_map
port_proof Option.getD_of_ne_none
port_proof Option.isNone_bind
port_proof Option.isNone_or
port_proof Option.isSome_bind
port_proof Option.isSome_or
port_proof Option.map_eq_bind by_reflexivity
port_proof Option.map_or
port_proof Option.merge_none_left
port_proof Option.merge_some_some by_reflexivity
port_proof Option.none_or by_reflexivity
port_proof Option.orElse_eq_or by_reflexivity
port_proof Option.or_assoc
port_proof Option.or_eq_bif
port_proof Option.or_none
port_proof Option.or_eq_orElse by_reflexivity
port_proof Option.or_self
port_proof Option.or_some
port_proof Option.pmap_pred_congr
port_proof Option.some_or by_reflexivity
port_proof Option.toList_none by_reflexivity
port_proof Option.toList_some by_reflexivity
port_proof Function.comp.eq_1 by_reflexivity
port_proof Option.bind.eq_1 by_reflexivity
port_proof Option.bind.eq_2 by_reflexivity
port_proof Option.le.eq_1 by_reflexivity
port_proof Option.le.eq_2 by_reflexivity
port_proof Option.le.eq_3 by_reflexivity
port_proof Option.le.eq_4 by_reflexivity
port_proof Option.lt.eq_1 by_reflexivity
port_proof Option.lt.eq_2 by_reflexivity
