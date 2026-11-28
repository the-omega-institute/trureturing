/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Core
import OmegaInit.SimpLemmas
import OmegaInit.Data.Nat.Basic

noncomputable section

port_inductive Acc
port_inductive WellFounded
port_definition Acc.ndrec
port_definition Acc.ndrecOn
port_proof Acc.inv
port_proof WellFounded.apply
port_definition WellFounded.recursion
port_proof WellFounded.induction
port_definition WellFounded.fixF
port_proof WellFounded.fixF_eq
port_definition WellFounded.fix
port_proof WellFounded.fix_eq
port_inductive WellFoundedRelation
port_definition WellFoundedRelation.rel
port_proof WellFoundedRelation.wf
port_private_declaration Nat.lt_wfRel.match_1
port_proof Nat.lt_wfRel._proof_3 by_constructive_casts
port_definition Nat.lt_wfRel with_native_code
port_definition Nat.strongRecOn

public section
namespace Nat
export _root_.Omega.Nat (lt_wfRel strongRecOn)
end Nat

port_definition WellFounded.wrap with_native_code
port_proof WellFounded.val_wrap by_reflexivity

namespace Omega

/-- Mark the value of a parameter during well-founded recursion. -/
@[expose, implicit_reducible] public def wfParam {α : Sort u} (a : α) : α := a

end Omega

port_definition WellFounded.Nat.eager with_native_code
port_proof WellFounded.Nat.fix.go._proof_1
port_proof WellFounded.Nat.fix._proof_1
port_definition WellFounded.Nat.fix.go
port_structural_code WellFounded.Nat.fix.go on_arg 5 using
  fun {α} {motive} h step fuel =>
    Nat.casesOn (motive := fun k => ∀ (x : α), Omega.Nat.lt (h x) k → motive x) fuel
      (fun x impossible => Omega.False.elim (Omega.Nat.not_succ_le_zero (h x) impossible))
      (fun k x bound => step x (fun y smaller =>
        Omega.WellFounded.Nat.fix.go h step k y
          (Omega.Nat.lt_of_lt_of_le smaller (Omega.Nat.le_of_lt_succ bound))))
port_proof WellFounded.Nat.eager_eq
port_proof WellFounded.Nat.fix._proof_2
port_definition WellFounded.Nat.fix with_native_code

/- WellFounded.Nat.fix.go_congr and WellFounded.Nat.fix_eq quantify over all
steps F. With the pinned fuel recursion both imply equality of all dependent
functions on an empty domain (MeasuredRecursion.ofFuelCongruence and
ofFixEquation). For a step preserving pointwise agreement of its smaller
recursive calls, goCongrOfRespectsCalls and fixEqOfRespectsCalls establish the
two conclusions with no axioms. The unrestricted statements remain open. -/
