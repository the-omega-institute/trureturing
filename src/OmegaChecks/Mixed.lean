module
import Mathlib.Data.Nat.Prime.Basic
import D5.Omega.ProjectiveOverlap

/-! Check both number types in one consumer of the existing mathlib environment. -/

open Omega renaming Nat → OmegaNat

example : Nat.Prime 2 := Nat.prime_two

example (n : OmegaNat) : Omega.Ratio.Equivalent (Omega.Projective.kappa n.succ n.succ)
    (Omega.Ratio.value Omega.Nat.one Omega.Nat.one.succ) :=
  D5.Omega.ProjectiveOverlap.diagonal_half n
