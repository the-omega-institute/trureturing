module
prelude
public import OmegaMath.Projective

public section

open Omega
open Omega.Projective

namespace OmegaChecks.ProjectiveOverlap

/-- For every positive coordinate magnitude, a diagonal ray has overlap one half. -/
theorem diagonal_half (k : Nat) :
    Ratio.Equivalent (kappa k.succ k.succ) (Ratio.value Nat.one Nat.one.succ) :=
  let h := Eq.map₂ kappa (Nat.one_mul k.succ) (Nat.one_mul k.succ)
  have square : Eq (Nat.one.mul Nat.one) Nat.one := Nat.one_mul Nat.one
  have two : Eq (Nat.one.add Nat.one) Nat.one.succ :=
    (Nat.add_succ Nat.one Nat.zero).trans (Omega.congrArg Nat.succ (Nat.add_zero Nat.one))
  have half : Eq (kappa Nat.one Nat.one) (Ratio.value Nat.one Nat.one.succ) :=
    Eq.map₂ Ratio.value square ((Eq.map₂ Nat.add square square).trans two)
  Eq.subst (motive := Ratio.Equivalent (kappa k.succ k.succ)) half
    (Eq.subst (motive := fun r => Ratio.Equivalent r (kappa Nat.one Nat.one)) h
      (kappa_scale Nat.one Nat.one k))

end OmegaChecks.ProjectiveOverlap
