/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Nat.Lemmas

/-!
The strict prime predicate and divisor characterization from
`Mathlib.Data.Nat.Prime.Defs`.
-/

@[expose] public section

namespace Omega.Nat

/-- A natural number at least two with only one and itself as divisors. -/
@[no_expose] def Prime (p : Nat) : Prop :=
  And (Nat.le zero.succ.succ p) (∀ m, Exists (fun k => Eq p (m.mul k)) →
    Or (Eq m zero.succ) (Eq m p))

theorem prime_def {p : Nat} :
    Iff (Prime p) (And (Nat.le zero.succ.succ p) (∀ m, Exists (fun k => Eq p (m.mul k)) →
      Or (Eq m zero.succ) (Eq m p))) :=
  Iff.intro (fun h => h) (fun h => h)

theorem Prime.two_le : ∀ {p : Nat}, Prime p → Nat.le zero.succ.succ p :=
  fun h => (prime_def.mp h).left

theorem Prime.one_lt {p : Nat} : Prime p → Nat.lt zero.succ p := Prime.two_le

theorem Prime.eq_one_or_self_of_dvd {p : Nat} (pp : Prime p) (m : Nat)
    (hm : Exists (fun k => Eq p (m.mul k))) : Or (Eq m zero.succ) (Eq m p) :=
  (prime_def.mp pp).right m hm

attribute [irreducible] Prime

end Omega.Nat

namespace Nat
export _root_.Omega.Nat (Prime prime_def)
end Nat
