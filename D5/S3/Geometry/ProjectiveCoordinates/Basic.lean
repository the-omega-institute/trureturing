/- GID: D5/S3/Geometry/ProjectiveCoordinates/Basic
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The chapter 39 overlap of homogeneous coordinates. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import D5.S0.Arithmetic.Exact.Ratio

/-!
Omega original.

The chapter 39 overlap of homogeneous coordinates.
-/

@[expose] public section

namespace Omega.Projective

/-- The squared overlap of [P:Q] with the reference point. The coordinates
are their magnitudes, since both coordinates enter only through their squares. -/
noncomputable def kappa (p q : Nat) : Ratio :=
  Ratio.value (Nat.mul q q) (Nat.add (Nat.mul p p) (Nat.mul q q))

end Omega.Projective
