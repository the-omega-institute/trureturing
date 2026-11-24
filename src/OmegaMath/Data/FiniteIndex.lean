/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Finite ordinals represented by zero and successor constructors indexed by their bound.
-/

@[expose] public section

namespace Omega

/-- An index below a given natural-number bound. -/
inductive FiniteIndex : Nat → Type where
  | zero {bound : Nat} : FiniteIndex bound.succ
  | succ {bound : Nat} : FiniteIndex bound → FiniteIndex bound.succ

end Omega
