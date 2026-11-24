/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega

def Iff (a b : Prop) : Prop := And (a → b) (b → a)

namespace Iff
theorem intro {a b : Prop} (mp : a → b) (mpr : b → a) : Iff a b := And.intro mp mpr

theorem mp {a b : Prop} (h : Iff a b) : a → b := And.left h

theorem mpr {a b : Prop} (h : Iff a b) : b → a := And.right h
def rec {a b : Prop} {motive : Iff a b → Sort u}
    (use : ∀ mp mpr, motive (intro mp mpr)) (h : Iff a b) : motive h :=
  use h.mp h.mpr
end Iff

def Exists {α : Sort u} (p : α → Prop) : Prop := ∀ r : Prop, (∀ w, p w → r) → r

theorem Exists.intro {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p :=
  fun _ use => use w h

theorem Exists.elim {α : Sort u} {p : α → Prop} {r : Prop}
    (h : Exists p) (use : ∀ w, p w → r) : r := h r use

theorem Exists.rec {α : Sort u} {p : α → Prop} {motive : Exists p → Prop}
    (use : ∀ w h, motive (Exists.intro w h)) (h : Exists p) : motive h :=
  h (motive h) use

namespace Nat

theorem succ.inj {a b : Nat} (h : Eq (succ a) (succ b)) : Eq a b :=
  congrArg pred h

theorem add_zero (a : Nat) : Eq (add a zero) a := Eq.refl

end Nat
end Omega
