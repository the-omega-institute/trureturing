/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

noncomputable section

@[expose] public section

port_inductive Option
port_inductive List

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

abbrev casesOn {a b : Prop} {motive : And a b → Sort u} (t : And a b)
    (intro : ∀ left right, motive (And.intro left right)) : motive t :=
  intro t.left t.right

protected abbrev recOn.{u} := @And.casesOn.{u}
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

abbrev casesOn {a b : Prop} {motive : Or a b → Prop} (t : Or a b)
    (inl : ∀ h, motive (Or.inl h)) (inr : ∀ h, motive (Or.inr h)) : motive t :=
  Or.rec (motive := motive) inl inr t

protected abbrev recOn := @Or.casesOn
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

/-- Induct upward from the lower bound. Cancellation of two successors reduces
the lower bound, while preserving the predicate on the upper bound. -/
private theorem fromLowerBound (n : Nat) :
    ∀ (P : Nat → Prop), P n → (∀ m, Nat.le n m → P m → P (succ m)) →
      ∀ a, Nat.le n a → P a :=
  Nat.rec (motive := fun n =>
      ∀ (P : Nat → Prop), P n → (∀ m, Nat.le n m → P m → P (succ m)) →
        ∀ a, Nat.le n a → P a)
    (fun P start step a _ =>
      Nat.rec (motive := P) start (fun m ih => step m (zero_le m) ih) a)
    (fun n smaller P start step a =>
      Nat.rec (motive := fun a => Nat.le (succ n) a → P a)
        (fun h => False.elim (not_succ_le_zero n h))
        (fun b _ h => smaller (fun k => P (succ k)) start
          (fun m hm ih => step (succ m) (succ_le_succ hm) ih) b (le_of_succ_le_succ h)) a) n

private theorem leRec {n : Nat} {motive : (a : Nat) → Nat.le n a → Prop}
    (refl : motive n Nat.le.refl)
    (step : ∀ {m : Nat} (h : Nat.le n m), motive m h → motive (succ m) (Nat.le.step h))
    {a : Nat} (t : Nat.le n a) : motive a t :=
  fromLowerBound n (fun m => ∀ h : Nat.le n m, motive m h) (fun _ => refl)
    (fun _ h ih _ => step h (ih h)) a t t

port_proof Nat.le.rec using leRec
port_proof Nat.le.casesOn
port_proof Nat.le.recOn

theorem succ_sub_succ_eq_sub (n m : Nat) : Eq (Nat.sub (succ n) (succ m)) (Nat.sub n m) :=
  Nat.rec (motive := fun i => Eq (pred (Nat.sub (succ n) i)) (Nat.sub n i))
    rfl (fun _ h => congrArg pred h) m

@[no_expose] protected def add : Nat → Nat → Nat :=
  fun a b => Nat.rec a (fun _ r => succ r) b

@[no_expose] protected def mul : Nat → Nat → Nat :=
  fun a => Nat.rec zero (fun _ r => Nat.add r a)

@[no_expose] protected def pow (m : Nat) : Nat → Nat :=
  Nat.rec (succ zero) (fun _ p => Nat.mul p m)

attribute [irreducible] Nat.add Nat.mul Nat.sub Nat.le Nat.pred Nat.pow

end Nat

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit

inductive Empty : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PEmpty : Sort u where

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

set_option linter.defProp false in
@[match_pattern] protected def HEq.rfl {α : Sort u} {a : α} : HEq a a := HEq.refl a

def id {α : Sort u} (a : α) : α := a

theorem id_eq (a : α) : Eq (id a) a := Omega.rfl

def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w}
    (f : β → δ) (g : α → β) : α → δ := fun x => f (g x)

def Function.const {α : Sort u} (β : Sort v) (a : α) : β → α := fun _ => a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1}
    (m : motive a) {b : α} (h : Eq a b) : motive b :=
  Eq.rec (motive := fun b _ => motive b) m h

abbrev Eq.ndrec_symm.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1}
    (m : motive a) {b : α} (h : Eq b a) : motive b := Eq.ndrec m h.symm

def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  Eq.rec (motive := fun β _ => β) a h

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : Eq f g) (a : α) : Eq (f a) (g a) := congrArg (fun f : (x : α) → β x => f a) h

theorem congrFun' {α : Sort u} {β : Sort v} {f g : α → β}
    (h : Eq f g) (a : α) : Eq (f a) (g a) := congrFun h a

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}
    (h₁ : Eq f₁ f₂) (h₂ : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  (congrFun h₁ a₁).trans (congrArg f₂ h₂)

theorem heq_of_eq (h : Eq a a') : HEq a a' :=
  Eq.subst h (HEq.refl a)

def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b := False.elim (h₂ h₁)

theorem Or.intro_left (b : Prop) (h : a) : Or a b := Or.inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b := Or.inr h

theorem Or.resolve_left (h : Or a b) (na : Not a) : b := h.elim (fun ha => absurd ha na) id

theorem Or.resolve_right (h : Or a b) (nb : Not b) : a := h.elim id (fun hb => absurd hb nb)

theorem Or.neg_resolve_left (h : Or (Not a) b) (ha : a) : b := h.elim (absurd ha) id

theorem Or.neg_resolve_right (h : Or a (Not b)) (nb : b) : a := h.elim id (absurd nb)

/-- Constructive nonemptiness with elimination into propositions. -/
@[class, no_expose] def Nonempty (α : Sort u) : Prop := ∀ p : Prop, (α → p) → p

theorem Nonempty.intro {α : Sort u} (val : α) : Nonempty α := fun _ f => f val

protected theorem Nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  h₁ p h₂

theorem Nonempty.rec {α : Sort u} {motive : Nonempty α → Prop}
    (intro : ∀ val, motive (Nonempty.intro val)) (t : Nonempty α) : motive t :=
  t.elim intro

attribute [irreducible] Nonempty

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  let align : ∀ (α β : Sort u) (a : α) (b : β), HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun α β a b he => @HEq.rec _ a
      (fun {β} b _ => (h : Eq α β) → Eq (cast h a) b)
      (fun _ => Eq.refl a) β b he
  align α α a a' h Omega.rfl

set_option checkBinderAnnotations false in
abbrev inferInstance {α : Sort u} [i : α] : α := i

set_option checkBinderAnnotations false in
abbrev «inferInstanceAs» (α : Sort u) [i : α] : α := i

set_option linter.unusedVariables.funArgs false in
@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α

@[reducible] def outParam (α : Sort u) : Sort u := α

@[reducible] def semiOutParam (α : Sort u) : Sort u := α

set_option linter.unusedVariables.funArgs false in
@[reducible] def namedPattern {α : Sort u} (x a : α) (h : Eq x a) : α := a

abbrev PUnit.casesOn.{v,u} {motive : (t : PUnit.{u}) → Sort v} (t : PUnit)
    (unit : motive PUnit.unit) : motive t := PUnit.rec unit t

abbrev Empty.casesOn (motive : (t : Empty) → Sort u) (t : Empty) : motive t :=
  Empty.rec motive t

abbrev PEmpty.casesOn.{v,u} (motive : (t : PEmpty.{u}) → Sort v) (t : PEmpty) : motive t :=
  PEmpty.rec motive t

abbrev Eq.casesOn.{v,u} := @Eq.recOn.{v,u}

abbrev HEq.casesOn.{v,u} := @HEq.recOn.{v,u}

protected abbrev Nonempty.recOn {α : Sort u} {motive : (t : Nonempty α) → Prop}
    (t : Nonempty α) (intro : ∀ val, motive (Nonempty.intro val)) : motive t :=
  Nonempty.rec intro t

abbrev Nonempty.casesOn {α : Sort u} {motive : (t : Nonempty α) → Prop}
    (t : Nonempty α) (intro : ∀ val, motive (Nonempty.intro val)) : motive t :=
  Nonempty.rec intro t

set_option linter.unusedVariables.funArgs false in
protected abbrev Empty.noConfusionType (P : Sort u) (t t' : Empty) : Sort u :=
  Empty.casesOn (fun _ => Sort u) t

protected abbrev Empty.noConfusion {P : Sort u} {t t' : Empty} (eq : Eq t t') :
    Empty.noConfusionType P t t' :=
  Eq.rec (motive := fun t' _ => Empty.noConfusionType P t t')
    (Empty.casesOn (fun t => Empty.noConfusionType P t t) t) eq

set_option linter.unusedVariables.funArgs false in
protected abbrev PEmpty.noConfusionType.{v,u} (P : Sort v) (t t' : PEmpty.{u}) : Sort v :=
  PEmpty.casesOn (fun _ => Sort v) t

protected abbrev PEmpty.noConfusion.{v,u} {P : Sort v} {t t' : PEmpty.{u}} (eq : Eq t t') :
    PEmpty.noConfusionType P t t' :=
  Eq.rec (motive := fun t' _ => PEmpty.noConfusionType P t t')
    (PEmpty.casesOn (fun t => PEmpty.noConfusionType P t t) t) eq

open Bool (false true)

def cond {α : Sort u} (c : Bool) (x y : α) : α := Bool.rec y x c

protected def Bool.dcond {α : Sort u} (c : Bool)
    (x : Eq c true → α) (y : Eq c false → α) : α :=
  Bool.rec (motive := fun b => (Eq b true → α) → (Eq b false → α) → α)
    (fun _ no => no Omega.rfl) (fun yes _ => yes Omega.rfl) c x y

def Bool.or (x y : Bool) : Bool := Bool.rec y true x

def Bool.and (x y : Bool) : Bool := Bool.rec false y x

def Bool.not (x : Bool) : Bool := Bool.rec true false x

def Bool.Internal.or (x y : Bool) : Bool := Bool.or x y

def Bool.Internal.and (x y : Bool) : Bool := Bool.and x y

def Bool.Internal.not : Bool → Bool := Bool.not

theorem Bool.and_eq_internalAnd : Eq Bool.and Bool.Internal.and := Omega.rfl

theorem Bool.or_eq_internalOr : Eq Bool.or Bool.Internal.or := Omega.rfl

theorem Bool.not_eq_internalNot : Eq Bool.not Bool.Internal.not := Omega.rfl

open Bool (or and not)

def Bool.beq (a b : Bool) : Bool := Bool.rec (Bool.not a) a b

abbrev Bool.Reflects : Bool → Prop → Prop :=
  fun b p => Bool.rec (motive := fun _ => Prop) (Not p) p b

theorem Bool.eq_false_of_ne_true : {b : Bool} → Not (Eq b true) → Eq b false :=
  fun {b} => Bool.rec (motive := fun b => Not (Eq b true) → Eq b false)
    (fun _ => Omega.rfl) (fun h => False.elim (h Omega.rfl)) b

theorem Bool.eq_true_of_ne_false : {b : Bool} → Not (Eq b false) → Eq b true :=
  fun {b} => Bool.rec (motive := fun b => Not (Eq b false) → Eq b true)
    (fun h => False.elim (h Omega.rfl)) (fun _ => Omega.rfl) b

theorem Bool.ne_false_of_eq_true : {b : Bool} → Eq b true → Not (Eq b false) :=
  fun h g => Eq.subst (motive := Bool.rec (motive := fun _ => Prop) True False) (g.symm.trans h) True.intro

theorem Bool.ne_true_of_eq_false : {b : Bool} → Eq b false → Not (Eq b true) :=
  fun h g => Bool.ne_false_of_eq_true g h

end Omega

namespace Omega

/-- A computation with access to a read-only environment. -/
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) := ρ → m α

def ReaderT.mk {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ρ → m α) : ReaderT ρ m α := x

def ReaderT.run {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : ReaderT ρ m α) (r : ρ) : m α :=
  x r

protected def ReaderT.adapt {ρ : Type u} {m : Type u → Type v} {ρ' α : Type u}
    (f : ρ' → ρ) : ReaderT ρ m α → ReaderT ρ' m α := fun x r => x (f r)

end Omega

namespace Omega.Option

protected def map {α : Type u} {β : Type v} (f : α → β) : Option α → Option β :=
  fun x => Option.casesOn (motive := fun _ => Option β) x none (fun a => some (f a))

def getD {α : Type u} (opt : Option α) (dflt : α) : α :=
  Option.casesOn (motive := fun _ => α) opt dflt (fun a => a)

end Omega.Option
