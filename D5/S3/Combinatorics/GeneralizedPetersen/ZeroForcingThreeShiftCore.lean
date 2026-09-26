/- GID: D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeShiftCore
   mirror-E: none(waiver:open-problem-resolution-has-no-escape-mirror)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Fin.Basic]
   utility: none
   digest: Column support and the two cyclic neighbour shifts. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary

def columns {n : Nat} (X : Finset (Bool × Fin n)) : Finset (Fin n) :=
  X.image Prod.snd

def occupiedVertices {n : Nat} (X : Finset (Bool × Fin n)) : Finset (Bool × Fin n) :=
  Finset.univ.product (columns X)

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeBoundary

namespace D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests

def positiveShift (n : Nat) [NeZero n] : Bool × Fin n ≃ Bool × Fin n where
  toFun v := (v.1, v.2 + Fin.ofNat n (if v.1 then 3 else 1))
  invFun v := (v.1, v.2 - Fin.ofNat n (if v.1 then 3 else 1))
  left_inv := by intro ⟨b, i⟩; simp
  right_inv := by intro ⟨b, i⟩; simp

def negativeShift (n : Nat) [NeZero n] : Bool × Fin n ≃ Bool × Fin n := (positiveShift n).symm

end D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeRequests
