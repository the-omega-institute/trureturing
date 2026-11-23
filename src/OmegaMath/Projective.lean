/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit

@[expose] public section

namespace Omega.Projective

/-- The squared overlap of [P:Q] with the reference point. The coordinates
are their magnitudes, since both coordinates enter only through their squares. -/
noncomputable def kappa (p q : Nat) : Ratio :=
  Ratio.value (Nat.mul q q) (Nat.add (Nat.mul p p) (Nat.mul q q))

/-- Any common positive scaling of the two coordinate magnitudes preserves the overlap. -/
theorem kappa_scale (p q k : Nat) :
    Ratio.Equivalent (kappa (Nat.mul p (Nat.succ k)) (Nat.mul q (Nat.succ k))) (kappa p q) :=
  let s := Nat.succ k
  let denom := Nat.add (Nat.mul p p) (Nat.mul q q)
  have hq := Nat.square_mul q s
  have hd := (Eq.map₂ Nat.add (Nat.square_mul p s) hq).trans
    (Nat.add_mul (Nat.mul p p) (Nat.mul q q) (Nat.mul s s)).symm
  have he := Eq.map₂ Ratio.value hq hd
  Eq.subst (fun r => Ratio.Equivalent r (kappa p q)) he.symm
    (Ratio.scale (Nat.mul q q) denom (Nat.add (Nat.mul s k) k))

end Omega.Projective
