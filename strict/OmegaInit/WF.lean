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
