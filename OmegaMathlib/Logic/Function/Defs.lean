/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Function

@[expose] public section

namespace Omega.Function

/-- A bijection is injective and surjective. -/
def Bijective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  And (Injective f) (Surjective f)

end Omega.Function
