/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

@[expose] public section

port_definition Function.curry with_native_code
port_definition Function.uncurry with_native_code

namespace Omega.Function

/-- Equal outputs of an injective function have equal inputs. -/
def Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ ⦃a b⦄, Eq (f a) (f b) → Eq a b

/-- Every element of the codomain of a surjective function has a preimage. -/
def Surjective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ b, Exists (fun a => Eq (f a) b)

/-- Applying the inverse after the forward map gives the original input. -/
def LeftInverse {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop :=
  ∀ a, Eq (g (f a)) a

/-- Applying the forward map after the inverse gives the original output. -/
def RightInverse {α : Sort u} {β : Sort v} (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g

theorem LeftInverse.injective {α : Sort u} {β : Sort v} {g : β → α} {f : α → β}
    : LeftInverse g f → Injective f :=
  fun h {a b} same => (h a).symm.trans ((congrArg g same).trans (h b))

theorem RightInverse.surjective {α : Sort u} {β : Sort v} {f : α → β} {g : β → α}
    (h : RightInverse g f) : Surjective f :=
  fun b => Exists.intro (g b) (h b)

theorem Injective.comp {α β γ} {g : β → γ} {f : α → β} (hg : Injective g) (hf : Injective f) :
    Injective (Function.comp g f) := fun {_ _} h => hf (hg h)

theorem Surjective.comp {α β γ} {g : β → γ} {f : α → β} (hg : Surjective g) (hf : Surjective f) :
    Surjective (Function.comp g f) := fun c =>
  (hg c).elim fun b hb => (hf b).elim fun a ha => Exists.intro a ((congrArg g ha).trans hb)

def HasLeftInverse {α β} (f : α → β) : Prop := Exists fun g : β → α => LeftInverse g f

def HasRightInverse {α β} (f : α → β) : Prop := Exists fun g : β → α => RightInverse g f

theorem HasLeftInverse.injective {α β} {f : α → β} : HasLeftInverse f → Injective f :=
  fun h => h.elim fun _ inv => LeftInverse.injective inv

theorem HasRightInverse.surjective {α β} {f : α → β} : HasRightInverse f → Surjective f :=
  fun h => h.elim fun _ inv => RightInverse.surjective inv

theorem rightInverse_of_injective_of_leftInverse {α β} {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x => injf (lfg (f x))

theorem leftInverse_of_surjective_of_rightInverse {α β} {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  (surjf y).elim fun x hx => (congrArg (Function.comp f g) hx.symm).trans ((congrArg f (rfg x)).trans hx)

theorem injective_id : Injective (@id α) := fun {_ _} h => h

theorem surjective_id : Surjective (@id α) := fun x => Exists.intro x rfl

variable {f : α → β}

theorem Injective.eq_iff (I : Injective f) {a b : α} : Iff (Eq (f a) (f b)) (Eq a b) :=
  Iff.intro (fun h => I h) (congrArg f)

theorem Injective.eq_iff' (I : Injective f) {a b : α} {c : β} (h : Eq (f b) c) :
    Iff (Eq (f a) c) (Eq a b) :=
  Iff.intro (fun e => I (e.trans h.symm)) (fun e => (congrArg f e).trans h)

theorem Injective.ne (hf : Injective f) {a₁ a₂ : α} : Ne a₁ a₂ → Ne (f a₁) (f a₂) :=
  fun ne e => ne (hf e)

theorem Injective.ne_iff (hf : Injective f) {x y : α} : Iff (Ne (f x) (f y)) (Ne x y) :=
  Iff.intro (fun ne e => ne (congrArg f e)) hf.ne

theorem Injective.ne_iff' (hf : Injective f) {x y : α} {z : β} (h : Eq (f y) z) :
    Iff (Ne (f x) z) (Ne x y) :=
  Iff.intro (fun ne e => ne ((congrArg f e).trans h)) (fun ne e => ne (hf (e.trans h.symm)))

end Omega.Function

port_proof Function.LeftInverse.eq_1 by_reflexivity
port_proof Function.RightInverse.eq_1 by_reflexivity
