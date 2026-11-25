prelude
import D5.S3.Geometry.ProjectiveCoordinates.Basic

open Omega

namespace Tests

-- These closed numerals are evaluated independently by each kernel.
set_option allowUnsafeReducibility true
attribute [local semireducible] Nat.add Nat.mul

private noncomputable def two := Nat.succ Nat.one

example : Eq (Projective.kappa Nat.zero Nat.one) (Ratio.value Nat.one Nat.one) :=
  Omega.rfl
example : Eq (Projective.kappa Nat.one Nat.one) (Ratio.value Nat.one two) :=
  Omega.rfl
example : Eq (Projective.kappa Nat.one Nat.zero) (Ratio.value Nat.zero Nat.one) :=
  Omega.rfl
example : Eq (Projective.kappa Nat.zero Nat.zero) Ratio.undefined := Omega.rfl
example : Ratio.Equivalent (Projective.kappa two two) (Ratio.value Nat.one two) :=
  Omega.rfl

end Tests
