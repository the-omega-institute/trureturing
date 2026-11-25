/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

noncomputable section

@[expose] public section

namespace Omega

/-- Equality and its eliminator are available in the strict environment. -/
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

@[match_pattern] abbrev rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

namespace Eq
theorem symm {a b : α} (h : Eq a b) : Eq b a :=
  Eq.rec (motive := fun b _ => Eq b a) rfl h

theorem trans {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  Eq.rec (motive := fun c _ => Eq a c) h₁ h₂

theorem subst {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.rec (motive := fun b _ => motive b) h₂ h₁
end Eq

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  Eq.rec (motive := fun a₂ _ => Eq (f a₁) (f a₂)) rfl h

inductive True : Prop where
  | intro

inductive False : Prop

def False.elim {C : Sort u} (h : False) : C := False.rec (motive := fun _ => C) h

def Not (a : Prop) : Prop := a → False

/-- Constructive conjunction with propositional elimination. -/
@[no_expose] def And (a b : Prop) : Prop := ∀ r : Prop, (a → b → r) → r

namespace And
theorem intro {a b : Prop} (left : a) (right : b) : And a b :=
  fun _ use => use left right

theorem left {a b : Prop} (self : And a b) : a := self a (fun ha _ => ha)

theorem right {a b : Prop} (self : And a b) : b := self b (fun _ hb => hb)
@[no_expose] def rec {a b : Prop} {motive : And a b → Sort u}
    (intro : ∀ left right, motive (And.intro left right)) (t : And a b) : motive t :=
  intro t.left t.right
end And

/-- Constructive disjunction with propositional elimination. -/
@[no_expose] def Or (a b : Prop) : Prop := ∀ r : Prop, (a → r) → (b → r) → r

namespace Or
theorem inl {a b : Prop} (h : a) : Or a b := fun _ left _ => left h

theorem inr {a b : Prop} (h : b) : Or a b := fun _ _ right => right h

theorem elim {a b c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  h c left right
theorem rec {a b : Prop} {motive : Or a b → Prop}
    (inl : ∀ h, motive (Or.inl h)) (inr : ∀ h, motive (Or.inr h))
    (t : Or a b) : motive t :=
  t (motive t) inl inr
end Or

attribute [irreducible] And And.rec Or

inductive Bool where
  | false
  | true

inductive Nat where
  | zero
  | succ (n : Nat)

namespace Nat

@[no_expose] def pred : Nat → Nat :=
  Nat.rec zero (fun n _ => n)

@[no_expose] protected def sub : Nat → Nat → Nat :=
  fun a => Nat.rec a (fun _ r => pred r)

/-- Comparison by removing one successor from both sides. -/
@[no_expose] protected def le (n : Nat) : Nat → Prop :=
  Nat.rec (motive := fun _ => Nat → Prop) (fun _ => True)
    (fun _ smaller n => Nat.rec (motive := fun _ => Prop) False (fun k _ => smaller k) n) n

protected def lt (n m : Nat) : Prop := Nat.le (succ n) m

theorem zero_le (n : Nat) : Nat.le zero n := True.intro

theorem succ_le_succ {n m : Nat} : Nat.le n m → Nat.le (succ n) (succ m) := fun h => h

theorem le_of_succ_le_succ {n m : Nat} : Nat.le (succ n) (succ m) → Nat.le n m := fun h => h

theorem not_succ_le_zero (n : Nat) : Not (Nat.le (succ n) zero) := fun h => h

protected theorem le_refl (n : Nat) : Nat.le n n :=
  Nat.rec (motive := fun k => Nat.le k k) True.intro (fun _ h => h) n

theorem le.refl {n : Nat} : Nat.le n n := Nat.le_refl n

theorem le.step {n m : Nat} : Nat.le n m → Nat.le n (succ m) := fun h =>
  (Nat.rec (motive := fun i => ∀ m, Nat.le i m → Nat.le i (succ m))
    (fun _ _ => True.intro)
    (fun n step m => Nat.rec (motive := fun x₀ => Nat.le (succ n) x₀ → Nat.le (succ n) (succ x₀))
      (fun h => False.elim h) (fun x₀ _ => step x₀) m) n) m h

protected theorem le_trans {n m k : Nat} : Nat.le n m → Nat.le m k → Nat.le n k := fun h g =>
  (Nat.rec (motive := fun n => ∀ m k, Nat.le n m → Nat.le m k → Nat.le n k)
    (fun _ _ _ _ => True.intro)
    (fun n trans m => Nat.rec (motive := fun m => ∀ k, Nat.le (succ n) m → Nat.le m k → Nat.le (succ n) k)
      (fun _ h _ => False.elim h)
      (fun m _ k => Nat.rec (motive := fun k =>
        Nat.le (succ n) (succ m) → Nat.le (succ m) k → Nat.le (succ n) k)
        (fun _ g => g) (fun k _ => trans m k) k) m) n) m k h g

protected theorem le_antisymm {n m : Nat} (h₁ : Nat.le n m) (h₂ : Nat.le m n) : Eq n m :=
  (Nat.rec (motive := fun n => ∀ m, Nat.le n m → Nat.le m n → Eq n m)
    (fun m => Nat.rec (motive := fun m => Nat.le zero m → Nat.le m zero → Eq zero m)
      (fun _ _ => rfl) (fun _ _ _ h₁ => False.elim h₁) m)
    (fun n antisymm m => Nat.rec (motive := fun m => Nat.le (succ n) m → Nat.le m (succ n) → Eq (succ n) m)
      (fun h₁ _ => False.elim h₁)
      (fun m _ h₁ h₂ => congrArg succ (antisymm m h₁ h₂)) m) n) m h₁ h₂

theorem succ_sub_succ_eq_sub (n m : Nat) : Eq (Nat.sub (succ n) (succ m)) (Nat.sub n m) :=
  Nat.rec (motive := fun i => Eq (pred (Nat.sub (succ n) i)) (Nat.sub n i))
    rfl (fun _ h => congrArg pred h) m

@[no_expose] protected def add : Nat → Nat → Nat :=
  fun a b => Nat.rec a (fun _ r => succ r) b

@[no_expose] protected def mul : Nat → Nat → Nat :=
  fun a => Nat.rec zero (fun _ r => Nat.add r a)

attribute [irreducible] Nat.add Nat.mul Nat.sub Nat.le Nat.pred

end Nat
end Omega
