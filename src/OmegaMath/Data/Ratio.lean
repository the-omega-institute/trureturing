/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.Nat

/-!
Omega original.

Exact nonnegative ratios with an explicit undefined value for a zero denominator.
-/

@[expose] public section

namespace Omega

namespace Eq
theorem map₂ (f : α → β → γ) {a b : α} {c d : β} (h : Eq a b) (g : Eq c d) :
    Eq (f a c) (f b d) :=
  (congrArg (fun x => f x c) h).trans (congrArg (f b) g)
end Eq

/-- A finite nonnegative ratio, or an undefined result for a zero denominator.
The second field of a fraction encodes a strictly positive denominator as its predecessor. -/
inductive Ratio where
  | undefined
  | fraction (numerator denominatorPred : Nat)

namespace Ratio

noncomputable def value (n d : Nat) : Ratio :=
  Nat.rec undefined (fun pred _ => fraction n pred) d

/-- Equality of exact values by cross multiplication; undefined agrees only with undefined. -/
def Equivalent (x y : Ratio) : Prop :=
  Ratio.rec (motive := fun _ => Prop)
    (Ratio.rec (motive := fun _ => Prop) True (fun _ _ => False) y)
    (fun a b => Ratio.rec (motive := fun _ => Prop) False
      (fun c d => Eq (Nat.mul a (Nat.succ d)) (Nat.mul c (Nat.succ b))) y) x

/-- Removing a common positive factor preserves the value, even for a zero numerator. -/
theorem scale (n d k : Nat) :
    Equivalent (value (Nat.mul n (Nat.succ k)) (Nat.mul d (Nat.succ k))) (value n d) :=
  Nat.rec (motive := fun d =>
    Equivalent (value (Nat.mul n (Nat.succ k)) (Nat.mul d (Nat.succ k))) (value n d))
    (Eq.subst (fun x => Equivalent (value (Nat.mul n (Nat.succ k)) x) undefined)
      (Nat.zero_mul (Nat.succ k)).symm True.intro)
    (fun p _ => (Nat.mul_right_comm n (Nat.succ k) (Nat.succ p)).trans
      (Nat.mul_assoc n (Nat.succ p) (Nat.succ k))) d

end Ratio
end Omega
