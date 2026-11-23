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
  Eq.subst (fun r => Ratio.Equivalent r (Ratio.value Nat.one Nat.one.succ)) h
    (kappa_scale Nat.one Nat.one k)

end OmegaChecks.ProjectiveOverlap
