/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Binary product represented by two functions on the one-proof proposition.
The projections evaluate those functions at its constructor.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A pair of values, stored as functions on `True`. -/
structure Product (α : Type u) (β : Type v) where
  first : True → α
  second : True → β

namespace Product

/-- Construct a pair from its two values. -/
def ofValues {α : Type u} {β : Type v} (a : α) (b : β) : Product α β :=
  ⟨fun _ => a, fun _ => b⟩

def fst {α : Type u} {β : Type v} (p : Product α β) : α :=
  p.first True.intro

def snd {α : Type u} {β : Type v} (p : Product α β) : β :=
  p.second True.intro

end Product
end Omega
