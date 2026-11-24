/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

@[expose] public section

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
    (h : LeftInverse g f) : Injective f :=
  fun {a b} same => (h a).symm.trans ((congrArg g same).trans (h b))

theorem RightInverse.surjective {α : Sort u} {β : Sort v} {g : β → α} {f : α → β}
    (h : RightInverse g f) : Surjective f :=
  fun b => Exists.intro (g b) (h b)

end Omega.Function
