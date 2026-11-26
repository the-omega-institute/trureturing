/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega

/-- Exception computations with separate success and error continuations. -/
def ExceptCpsT (ε : Type u) (m : Type u → Type v) (α : Type u) :=
  (β : Type u) → (α → m β) → (ε → m β) → m β

def ExceptCpsT.runK {m : Type u → Type v} {β ε α : Type u}
    (x : ExceptCpsT ε m α) (ok : α → m β) (error : ε → m β) : m β := x β ok error

end Omega
