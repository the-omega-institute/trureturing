/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module
prelude

noncomputable section

port_inductive Acc
port_inductive WellFounded

namespace Omega

/-- Mark the value of a parameter during well-founded recursion. -/
@[expose, implicit_reducible] public def wfParam {α : Sort u} (a : α) : α := a

end Omega
