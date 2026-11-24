/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Finite lists with an append-at-the-end constructor.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A finite list built by appending one element at a time. -/
inductive SnocList (A : Type u) where
  | empty
  | extend (initial : SnocList A) (last : True → A)

namespace SnocList

/-- Append a final element. -/
def pushBack {A : Type u} (initial : SnocList A) (last : A) : SnocList A :=
  .extend initial (fun _ => last)

end SnocList
end Omega
