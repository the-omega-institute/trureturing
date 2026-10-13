/- GID: D5/S3/FiniteGroups/SL2F5CentralSquareCertificate
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/SL2F5CentralSquareCertificate
   mirror-E: none(waiver:finite-sl2f5-certificate)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup]
   utility: none
   digest: Finite SL2 over F5 has only the two square roots of identity, with the explicit transport matrices. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.FiniteGroups.SL2F5CentralSquareCertificate

private abbrev Matrix2 := Matrix (Fin 2) (Fin 2) (ZMod 5)

private def identity : Matrix2 := 1
private def negativeIdentity : Matrix2 := -1

private def matrix (a b c d : ZMod 5) : Matrix2 := !![a, b; c, d]

private def u : Matrix2 := !![0, 1; 4, 1]
private def v : Matrix2 := !![1, 1; 0, 1]
private def vInverse : Matrix2 := !![1, 4; 0, 1]
private def ell : Matrix2 := vInverse * u ^ 2
private def h : Matrix2 := v ^ 2 * u

/--
A finite kernel computation for the central-involution obstruction.  The first
conjunct enumerates all determinant-one two-by-two matrices over `ZMod 5` and
shows that a square root of the identity is either `I` or `-I`.  The remaining
conjuncts check the explicit matrices used for the low and high return words.
This is only the stated finite certificate; it does not formalize the general
face-transport construction or the projective quotient.
-/
theorem sl2f5_central_square_certificate :
    (∀ (a b c d : ZMod 5),
      a * d - b * c = 1 →
      matrix a b c d * matrix a b c d = identity →
      matrix a b c d = identity ∨ matrix a b c d = negativeIdentity) ∧
    negativeIdentity ≠ identity ∧
    Matrix.det u = 1 ∧
    Matrix.det v = 1 ∧
    Matrix.det vInverse = 1 ∧
    vInverse * v = identity ∧
    v * vInverse = identity ∧
    ell = !![0, 1; 4, 0] ∧
    h = !![3, 3; 4, 1] ∧
    ell ^ 2 = negativeIdentity ∧
    h ^ 3 = identity ∧
    u ^ 3 = negativeIdentity ∧
    v ^ 5 = identity := by
  decide +kernel

end D5.S3.FiniteGroups.SL2F5CentralSquareCertificate
