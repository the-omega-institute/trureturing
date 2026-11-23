/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Prelude

@[expose] public section

namespace Omega.Nat

theorem add_zero (a : Nat) : Eq (add a zero) a := Eq.refl

end Omega.Nat
