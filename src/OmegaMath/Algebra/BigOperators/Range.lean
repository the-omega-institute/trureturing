/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Ordered finite sums over natural-number ranges.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- Sum the values at indices below the bound in increasing index order. -/
def sumRange {A : Type u} (zero : A) (add : A → A → A) (value : Nat → A) : Nat → A :=
  Nat.rec zero (fun index total => add total (value index))

end Omega
