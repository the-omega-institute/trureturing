/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude

noncomputable section

namespace Omega

/-- Apply a dependently typed function to a value. -/
@[expose] public def letFun {α : Sort u} {β : α → Sort v} (v : α) (f : (x : α) → β x) : β v :=
  f v

end Omega
