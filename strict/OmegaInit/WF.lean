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
port_definition WellFounded.wrap with_native_code
port_proof WellFounded.val_wrap by_reflexivity

namespace Omega

/-- Mark the value of a parameter during well-founded recursion. -/
@[expose, implicit_reducible] public def wfParam {α : Sort u} (a : α) : α := a

end Omega

port_definition WellFounded.Nat.eager
port_proof WellFounded.Nat.fix.go._proof_1
port_proof WellFounded.Nat.fix._proof_1
port_definition WellFounded.Nat.fix.go
port_proof WellFounded.Nat.eager_eq
port_proof WellFounded.Nat.fix._proof_2
port_definition WellFounded.Nat.fix
