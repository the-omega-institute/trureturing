/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary
   generality: I
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeBoundary
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Basic]
   utility: none
   digest: Occupied columns give a lower bound on the external boundary of a Petersen vertex set. -/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Group.Fin.Basic
import D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeShiftCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary

open D5.S3.Combinatorics.GeneralizedPetersen.ParityRefutation (gp)

def externalBoundary (n : Nat) (X : Finset (Bool × Fin n)) : Finset (Bool × Fin n) :=
  Finset.univ.filter fun v => v ∉ X ∧ ∃ u ∈ X, (gp n 3).Adj u v

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary
