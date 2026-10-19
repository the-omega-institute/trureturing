/- GID: D5/S3/Geometry/Hyperideal/SL2F5ExplicitPacket
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/SL2F5ExplicitPacket
   mirror-E: none(waiver:finite-sl2f5-explicit-packet)
   anchors: []
   utility: none
   digest: Explicit SL2(F5) matrices realize the return-word identities and the group has order 120. -/

/-
proof_shape: sl2_five_explicit_relations and sl2_five_cardinality: content
admission_basis: escape-witness.
escape_witness: the declarations compute new identities for the displayed
matrices over ZMod 5 and the exact finite cardinality of their determinant-one
matrix group; these facts are not instances of the frozen square-one theorem.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19034
-/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Defs

open scoped MatrixGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Geometry.Hyperideal.SL2F5ExplicitPacket

abbrev G := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)

def u : G := ⟨!![0, 1; 4, 1], by decide⟩

def v : G := ⟨!![1, 1; 0, 1], by decide⟩

def lowReturn : G := v⁻¹ * u ^ 2

def highReturn : G := v ^ 2 * u

def centralReturn : G := v * u ^ 3

set_option maxHeartbeats 4000000 in
theorem sl2_five_explicit_relations :
    lowReturn ^ 2 = -1 ∧
      lowReturn ^ 4 = 1 ∧
      lowReturn ≠ 1 ∧
      highReturn ^ 3 = 1 ∧
      highReturn ≠ 1 ∧
      u ^ 3 = -1 ∧
      v ^ 5 = 1 ∧
      u * v = lowReturn ∧
      centralReturn = -v ∧
      centralReturn ^ 5 = -1 := by
  decide

set_option maxHeartbeats 4000000 in
theorem sl2_five_cardinality : Fintype.card G = 120 := by
  decide

end D5.S3.Geometry.Hyperideal.SL2F5ExplicitPacket
