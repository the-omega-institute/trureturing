/- GID: D5/S0/Arithmetic/FiniteSums/Range
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Ordered finite sums over natural-number ranges. -/

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
