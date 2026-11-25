/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.QuadraticExt.Ring

/-!
Omega original.

Finite coordinate sequences and their sums, including sums over all pairs of
positions with the first position strictly before the second.
-/

noncomputable section

@[expose] public section

namespace Omega.LagrangeSchur

/-- A finite sequence, including the empty sequence. -/
inductive Sequence (α : Type) where
  | nil
  /-- The head is stored as a function and read at `false`. Use `cons` to prepend a value. -/
  | consFn (head : Bool → α) (tail : Sequence α)

namespace Sequence

def cons {α : Type} (head : α) (tail : Sequence α) : Sequence α :=
  consFn (fun _ => head) tail

def map {α β : Type} (f : α → β) (xs : Sequence α) : Sequence β :=
  Sequence.rec nil (fun x _ ys => cons (f (x .false)) ys) xs

def sum {α β : Type} (zero : β) (add : β → β → β) (f : α → β)
    (xs : Sequence α) : β :=
  Sequence.rec zero (fun x _ rest => add (f (x .false)) rest) xs

/-- Sum over the pairs of distinct positions `i < j` in sequence order. -/
def sumPairs {α β : Type} (zero : β) (add : β → β → β) (f : α → α → β)
    (xs : Sequence α) : β :=
  Sequence.rec zero (fun x tail rest => add (sum zero add (f (x .false)) tail) rest) xs

/-- A property holding at each position of the sequence. -/
def All {α : Type} (p : α → Prop) (xs : Sequence α) : Prop :=
  Sequence.rec (motive := fun _ => Prop) True (fun x _ rest => And (p (x .false)) rest) xs

variable {α A : Type} {relation : A → A → Prop} (r : CommRingOps A relation)
variable (law : r.Laws)

theorem all_of_forall (p : α → Prop) (h : ∀ x, p x) (xs : Sequence α) : All p xs :=
  Sequence.rec (motive := fun xs => All p xs)
    True.intro (fun x _ ih => And.intro (h (x .false)) ih) xs

theorem all_imp (p q : α → Prop) (h : ∀ x, p x → q x) (xs : Sequence α) :
    All p xs → All q xs :=
  Sequence.rec (motive := fun xs => All p xs → All q xs)
    (fun _ => True.intro) (fun x _ ih hx => And.intro (h (x .false) hx.left) (ih hx.right)) xs

include law

theorem sum_congr (f g : α → A) (xs : Sequence α) :
    All (fun x => r.eqv (f x) (g x)) xs →
      r.eqv (sum r.zero r.add f xs) (sum r.zero r.add g xs) :=
  Sequence.rec (motive := fun xs => All (fun x => r.eqv (f x) (g x)) xs →
    r.eqv (sum r.zero r.add f xs) (sum r.zero r.add g xs))
    (fun _ => law.refl r.zero) (fun _ _ ih h => law.add_congr h.left (ih h.right)) xs

theorem sum_add (f g : α → A) (xs : Sequence α) :
    r.eqv (sum r.zero r.add (fun x => r.add (f x) (g x)) xs)
      (r.add (sum r.zero r.add f xs) (sum r.zero r.add g xs)) :=
  let s := fun f xs => sum r.zero r.add f xs
  Sequence.rec (motive := fun xs =>
    r.eqv (s (fun x => r.add (f x) (g x)) xs) (r.add (s f xs) (s g xs)))
    (law.symm (law.add_zero r.zero))
    (fun x tail ih =>
      law.trans (law.add_congr (law.refl (r.add (f (x .false)) (g (x .false)))) ih)
        (law.add_add_add_comm (f (x .false)) (g (x .false)) (s f tail) (s g tail))) xs

theorem sum_mul_right (f : α → A) (a : A) (xs : Sequence α) :
    r.eqv (sum r.zero r.add (fun x => r.mul (f x) a) xs)
      (r.mul (sum r.zero r.add f xs) a) :=
  Sequence.rec (motive := fun xs =>
    r.eqv (sum r.zero r.add (fun x => r.mul (f x) a) xs) (r.mul (sum r.zero r.add f xs) a))
    (law.symm (law.zero_mul a))
    (fun x tail ih =>
      law.trans (law.add_congr (law.refl (r.mul (f (x .false)) a)) ih)
        (law.symm (law.add_mul (f (x .false)) (sum r.zero r.add f tail) a))) xs

theorem sum_map {β : Type} (f : α → β) (g : β → A) (xs : Sequence α) :
    r.eqv (sum r.zero r.add g (map f xs)) (sum r.zero r.add (fun x => g (f x)) xs) :=
  Sequence.rec (motive := fun xs =>
    r.eqv (sum r.zero r.add g (map f xs)) (sum r.zero r.add (fun x => g (f x)) xs))
    (law.refl r.zero) (fun x _ ih => law.add_congr (law.refl (g (f (x .false)))) ih) xs

omit law

theorem sum_closed (p : A → Prop) (zero : p r.zero)
    (add : ∀ a b, p a → p b → p (r.add a b)) (f : α → A) (xs : Sequence α) :
    All (fun x => p (f x)) xs → p (sum r.zero r.add f xs) :=
  Sequence.rec (motive := fun xs => All (fun x => p (f x)) xs → p (sum r.zero r.add f xs))
    (fun _ => zero)
    (fun x tail ih h => add (f (x .false)) (sum r.zero r.add f tail) h.left (ih h.right)) xs

theorem sum_pairs_closed (p : A → Prop) (zero : p r.zero)
    (add : ∀ a b, p a → p b → p (r.add a b)) (f : α → α → A)
    (h : ∀ x y, p (f x y)) (xs : Sequence α) :
    p (sumPairs r.zero r.add f xs) :=
  Sequence.rec (motive := fun xs => p (sumPairs r.zero r.add f xs)) zero
    (fun x tail ih =>
      add (sum r.zero r.add (f (x .false)) tail) (sumPairs r.zero r.add f tail)
        (sum_closed r p zero add (f (x .false)) tail (all_of_forall _ (h (x .false)) tail)) ih) xs

end Sequence

/-- Two coordinates selected by `false` and `true`. -/
structure CoordinatePair (α : Type) where
  coordinate : Bool → α

namespace CoordinatePair

def of {α : Type} (u v : α) : CoordinatePair α := ⟨fun i => Bool.rec u v i⟩

def u {α : Type} (p : CoordinatePair α) : α := p.coordinate .false

def v {α : Type} (p : CoordinatePair α) : α := p.coordinate .true

end CoordinatePair

end Omega.LagrangeSchur
