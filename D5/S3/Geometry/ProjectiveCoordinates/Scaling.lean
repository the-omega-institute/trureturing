/- GID: D5/S3/Geometry/ProjectiveCoordinates/Scaling
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Positive scaling preserves the chapter 39 overlap of homogeneous coordinates. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude
public import D5.S3.Geometry.ProjectiveCoordinates.Basic

/-!
Omega original.

Positive scaling preserves the chapter 39 overlap of homogeneous coordinates.
-/

public section

namespace Omega.Projective

/-- Any common positive scaling of the two coordinate magnitudes preserves the overlap. -/
theorem kappa_scale (p q k : Nat) :
    Ratio.Equivalent (kappa (Nat.mul p (Nat.succ k)) (Nat.mul q (Nat.succ k))) (kappa p q) :=
  let s := Nat.succ k
  let denom := Nat.add (Nat.mul p p) (Nat.mul q q)
  have hq := Nat.square_mul q s
  have hd := (Eq.map₂ Nat.add (Nat.square_mul p s) hq).trans
    (Nat.add_mul (Nat.mul p p) (Nat.mul q q) (Nat.mul s s)).symm
  have he := Eq.map₂ Ratio.value hq hd
  have hs := (Nat.mul_succ s k).trans (Nat.add_succ (s.mul k) k)
  Eq.subst (motive := fun r => Ratio.Equivalent r (kappa p q)) he.symm
    (Eq.subst (motive := fun factor =>
      Ratio.Equivalent (Ratio.value ((q.mul q).mul factor) (denom.mul factor)) (kappa p q))
      hs.symm (Ratio.scale (q.mul q) denom ((s.mul k).add k)))

end Omega.Projective
