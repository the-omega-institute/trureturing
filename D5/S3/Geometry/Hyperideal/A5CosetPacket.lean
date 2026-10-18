/- GID: D5/S3/Geometry/Hyperideal/A5CosetPacket
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/A5CosetPacket
   mirror-E: none(waiver:explicit-a5-coset-packet)
   anchors: []
   utility: none
   digest: The explicit twelve-point return permutations have six 2-cycles and four 3-cycles. -/

/-
proof_shape: low_return_has_six_two_cycles and high_return_has_four_three_cycles: content
admission_basis: escape-witness.
escape_witness: each theorem is a new finite permutation computation from the supplied
12-point tables; the period-cardinality facts are not obtained by instantiating an
existing frozen theorem.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19015
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.A5CosetPacket

abbrev Point := Fin 12

def U : Equiv.Perm Point :=
  { toFun := ![1, 2, 0, 5, 3, 4, 7, 8, 6, 11, 9, 10]
    invFun := ![2, 0, 1, 4, 5, 3, 8, 6, 7, 10, 11, 9]
    left_inv := by decide
    right_inv := by decide }

def V : Equiv.Perm Point :=
  { toFun := ![0, 2, 8, 7, 6, 10, 1, 5, 4, 3, 9, 11]
    invFun := ![0, 6, 1, 9, 8, 7, 4, 3, 2, 10, 5, 11]
    left_inv := by decide
    right_inv := by decide }

def lowReturn : Equiv.Perm Point := U ^ 2 * V⁻¹

def highReturn : Equiv.Perm Point := U * V ^ 2

def periodicPoints (f : Equiv.Perm Point) (n : Nat) : Finset Point :=
  Finset.univ.filter (fun x => (f^[n]) x = x)

theorem low_return_has_six_two_cycles :
    (periodicPoints lowReturn 2).card = 12 ∧
      (periodicPoints lowReturn 1).card = 0 := by
  decide

theorem high_return_has_four_three_cycles :
    (periodicPoints highReturn 3).card = 12 ∧
      (periodicPoints highReturn 1).card = 0 := by
  decide

end D5.S3.Geometry.Hyperideal.A5CosetPacket
