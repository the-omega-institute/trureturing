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

protected def False.elim {α : Sort u} (h : False) : α := False.rec (motive := fun _ => α) h

def Not (a : Prop) : Prop := a → False

/-- Constructive conjunction with propositional elimination. -/
def And (a b : Prop) : Prop := ∀ r : Prop, (a → b → r) → r

namespace And
theorem intro {a b : Prop} (ha : a) (hb : b) : And a b :=
  fun _ use => use ha hb

theorem left {a b : Prop} (h : And a b) : a := h a (fun ha _ => ha)

theorem right {a b : Prop} (h : And a b) : b := h b (fun _ hb => hb)
def rec {a b : Prop} {motive : And a b → Sort u}
    (use : ∀ ha hb, motive (intro ha hb)) (h : And a b) : motive h :=
  use h.left h.right
end And

/-- Constructive disjunction with propositional elimination. -/
def Or (a b : Prop) : Prop := ∀ r : Prop, (a → r) → (b → r) → r

namespace Or
theorem inl {a b : Prop} (ha : a) : Or a b := fun _ left _ => left ha

theorem inr {a b : Prop} (hb : b) : Or a b := fun _ _ right => right hb

theorem elim {a b r : Prop} (h : Or a b) (left : a → r) (right : b → r) : r :=
  h r left right
theorem rec {a b : Prop} {motive : Or a b → Prop}
    (left : ∀ ha, motive (inl ha)) (right : ∀ hb, motive (inr hb))
    (h : Or a b) : motive h :=
  h (motive h) left right
end Or

inductive Bool where
  | false
  | true

inductive Nat where
  | zero
  | succ (n : Nat)

namespace Nat

def pred (a : Nat) : Nat :=
  Nat.rec zero (fun n _ => n) a

def sub (a b : Nat) : Nat :=
  Nat.rec a (fun _ r => pred r) b

/-- Comparison by removing one successor from both sides. -/
def le (a b : Nat) : Prop :=
  Nat.rec (motive := fun _ => Nat → Prop) (fun _ => True)
    (fun _ smaller n => Nat.rec (motive := fun _ => Prop) False (fun k _ => smaller k) n) a b

def lt (a b : Nat) : Prop := le (succ a) b

theorem zero_le (a : Nat) : le zero a := True.intro

theorem succ_le_succ {a b : Nat} (h : le a b) : le (succ a) (succ b) := h

theorem le_of_succ_le_succ {a b : Nat} (h : le (succ a) (succ b)) : le a b := h

theorem not_succ_le_zero (a : Nat) : Not (le (succ a) zero) := fun h => h

theorem le.refl (a : Nat) : le a a :=
  Nat.rec (motive := fun n => le n n) True.intro (fun _ h => h) a

theorem le.step {a b : Nat} (h : le a b) : le a (succ b) :=
  (Nat.rec (motive := fun n => ∀ b, le n b → le n (succ b))
    (fun _ _ => True.intro)
    (fun a step b => Nat.rec (motive := fun k => le (succ a) k → le (succ a) (succ k))
      (fun h => False.elim h) (fun k _ => step k) b) a) b h

theorem le_trans {a b c : Nat} (h : le a b) (g : le b c) : le a c :=
  (Nat.rec (motive := fun a => ∀ b c, le a b → le b c → le a c)
    (fun _ _ _ _ => True.intro)
    (fun a trans b => Nat.rec (motive := fun b => ∀ c, le (succ a) b → le b c → le (succ a) c)
      (fun _ h _ => False.elim h)
      (fun b _ c => Nat.rec (motive := fun c =>
        le (succ a) (succ b) → le (succ b) c → le (succ a) c)
        (fun _ g => g) (fun c _ => trans b c) c) b) a) b c h g

theorem le_antisymm {a b : Nat} (h : le a b) (g : le b a) : Eq a b :=
  (Nat.rec (motive := fun a => ∀ b, le a b → le b a → Eq a b)
    (fun b => Nat.rec (motive := fun b => le zero b → le b zero → Eq zero b)
      (fun _ _ => Eq.refl) (fun _ _ _ h => False.elim h) b)
    (fun a antisymm b => Nat.rec (motive := fun b => le (succ a) b → le b (succ a) → Eq (succ a) b)
      (fun h _ => False.elim h)
      (fun b _ h g => congrArg succ (antisymm b h g)) b) a) b h g

theorem succ_sub_succ_eq_sub (a b : Nat) : Eq (sub (succ a) (succ b)) (sub a b) :=
  Nat.rec (motive := fun n => Eq (pred (sub (succ a) n)) (sub a n))
    Eq.refl (fun _ h => congrArg pred h) b

def add (a b : Nat) : Nat :=
  Nat.rec a (fun _ r => succ r) b

def mul (a b : Nat) : Nat :=
  Nat.rec zero (fun _ r => add r a) b

end Nat
end Omega
