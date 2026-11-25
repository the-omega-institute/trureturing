/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega

@[no_expose] def Iff (a b : Prop) : Prop := And (a → b) (b → a)

namespace Iff
theorem intro {a b : Prop} (mp : a → b) (mpr : b → a) : Iff a b := And.intro mp mpr

theorem mp {a b : Prop} (self : Iff a b) : a → b := And.left self

theorem mpr {a b : Prop} (self : Iff a b) : b → a := And.right self
@[no_expose] def rec {a b : Prop} {motive : Iff a b → Sort u}
    (intro : ∀ mp mpr, motive (Iff.intro mp mpr)) (t : Iff a b) : motive t :=
  intro t.mp t.mpr
end Iff

@[no_expose] def Exists {α : Sort u} (p : α → Prop) : Prop := ∀ r : Prop, (∀ w, p w → r) → r

theorem Exists.intro {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p :=
  fun _ use => use w h

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h₁ : Exists p) (h₂ : ∀ a, p a → b) : b := h₁ b h₂

theorem Exists.rec {α : Sort u} {p : α → Prop} {motive : Exists p → Prop}
    (intro : ∀ w h, motive (Exists.intro w h)) (t : Exists p) : motive t :=
  t (motive t) intro

attribute [irreducible] Iff Iff.rec Exists

namespace Nat

attribute [local semireducible] Nat.add Nat.pred

theorem succ.inj {m n : Nat} : Eq (succ m) (succ n) → Eq m n := fun h =>
  congrArg pred h

protected theorem add_zero (n : Nat) : Eq (Nat.add n zero) n := Omega.rfl

end Nat
end Omega
