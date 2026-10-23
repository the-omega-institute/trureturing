/- GID: D5/S3/Geometry/Gluing/A5TwelveCosetFiniteCertificate
   generality: I
   mirror-B: D5/B/S3/Geometry/Gluing/A5TwelveCosetFiniteCertificate
   mirror-E: none(waiver:finite-a5-instance)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.List, mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Type]
   utility: none
   digest: A finite twelve-point permutation certificate computes the A5 boundary counts. -/

import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Geometry.Gluing.A5TwelveCosetFiniteCertificate

private abbrev Point := Fin 12
private abbrev Permutation := Equiv.Perm Point

private def lowGenerator : Permutation :=
  ([0, 1, 2] : List Point).formPerm *
  ([3, 5, 4] : List Point).formPerm *
  ([6, 7, 8] : List Point).formPerm *
  ([9, 11, 10] : List Point).formPerm

private def highGenerator : Permutation :=
  ([1, 2, 8, 4, 6] : List Point).formPerm *
  ([3, 7, 5, 10, 9] : List Point).formPerm

private def lowImageTable : Point → Point :=
  ![1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10]

private def highImageTable : Point → Point :=
  ![0, 2, 8, 7, 6, 10, 1, 5, 4, 3, 9, 11]

private def lowReturn : Permutation := lowGenerator ^ 2 * highGenerator⁻¹
private def highReturn : Permutation := lowGenerator * highGenerator ^ 2

private def vertexCount : ℕ :=
  2 * lowReturn.cycleType.card + 2 * highReturn.cycleType.card

private def edgeCount : ℕ := 6 * 12
private def faceCount : ℕ := 4 * 12
private def eulerCharacteristic : ℤ :=
  (vertexCount : ℤ) - edgeCount + faceCount
private def boundaryGenus : ℕ :=
  1 + 12 - vertexCount / 2

/--
The supplied image tables, cycle decompositions, and link counts all hold by a
finite kernel computation.  This certifies only this twelve-point instance; it
does not assert the general noncommutative transport theorem or a geometric
realization beyond the stated finite data.
-/
theorem a5_finite_cycle_certificate :
    (∀ i, lowGenerator i = lowImageTable i) ∧
    (∀ i, highGenerator i = highImageTable i) ∧
    lowGenerator.cycleType = ({3, 3, 3, 3} : Multiset ℕ) ∧
    highGenerator.cycleType = ({5, 5} : Multiset ℕ) ∧
    lowReturn.cycleType = ({2, 2, 2, 2, 2, 2} : Multiset ℕ) ∧
    highReturn.cycleType = ({3, 3, 3, 3} : Multiset ℕ) ∧
    vertexCount = 20 ∧
    edgeCount = 72 ∧
    faceCount = 48 ∧
    eulerCharacteristic = -4 ∧
    boundaryGenus = 3 := by
  decide +kernel

end D5.S3.Geometry.Gluing.A5TwelveCosetFiniteCertificate
