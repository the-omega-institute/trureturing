/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

@[expose] public section

namespace Omega

/-- Equality and its eliminator are available in the strict environment. -/
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

namespace Eq
theorem symm {a b : α} (h : Eq a b) : Eq b a :=
  Eq.rec (motive := fun b _ => Eq b a) Eq.refl h

theorem trans {a b c : α} (h : Eq a b) (g : Eq b c) : Eq a c :=
  Eq.rec (motive := fun c _ => Eq a c) h g

theorem subst (P : α → Prop) {a b : α} (h : Eq a b) (p : P a) : P b :=
  Eq.rec (motive := fun b _ => P b) p h
end Eq

theorem congrArg (f : α → β) {a b : α} (h : Eq a b) : Eq (f a) (f b) :=
  Eq.rec (motive := fun b _ => Eq (f a) (f b)) Eq.refl h

inductive True : Prop where
  | intro

inductive False : Prop

inductive Nat where
  | zero
  | succ (n : Nat)

namespace Nat

noncomputable def add (a b : Nat) : Nat :=
  Nat.rec a (fun _ r => succ r) b

noncomputable def mul (a b : Nat) : Nat :=
  Nat.rec zero (fun _ r => add r a) b

end Nat
end Omega
