/- GID: D5/S3/VertexAlgebra/FiniteDefectCharacterCarry
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FiniteDefectCharacterCarry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind; instance=D5/S3/VertexAlgebra/FiniteDefectCharacterCarry.carry_is_wedge
   digest: All eight rank-three sign choices have the same determinant-valued character carry. -/

/-
proof_shape: carry_is_wedge: content
escape_witness: The quadratic part of the sign table survives polarization as the
  three-coordinate wedge; every alternating correction cancels in the carry.
admission_basis: escape-witness
Direct frozen dependencies: none.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import D5.S3.VertexAlgebra.CharacterCarryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.VertexAlgebra.FiniteDefectCharacterCarry

abbrev E := Fin 3 → ZMod 2

def basis (i : Fin 3) : E := fun j => if i = j then 1 else 0

def f0 (g h : E) : ZMod 2 :=
  g 0 * h 0 + g 1 * h 1 + g 2 * h 2 +
  g 0 * h 1 + g 0 * h 2 + g 1 * h 2 +
  g 0 * g 1 * h 2 + g 0 * g 2 * h 1 + g 1 * g 2 * h 0

def alternating (mask g h : E) : ZMod 2 :=
  mask 0 * (g 0 * h 1 + g 1 * h 0) +
  mask 1 * (g 0 * h 2 + g 2 * h 0) +
  mask 2 * (g 1 * h 2 + g 2 * h 1)

def sign (mask g h : E) : ZMod 2 := f0 g h + alternating mask g h

def ell (mask g : E) : E := fun i => sign mask g (basis i)

def wedge (g h : E) : E := fun i =>
  if i = 0 then g 1 * h 2 + g 2 * h 1
  else if i = 1 then g 0 * h 2 + g 2 * h 0
  else g 0 * h 1 + g 1 * h 0

def dot (g h : E) : ZMod 2 := g 0 * h 0 + g 1 * h 1 + g 2 * h 2

def determinant (g h k : E) : ZMod 2 := dot (wedge g h) k

set_option maxHeartbeats 0 in
-- The closed decision procedure checks all eight masks and all ordered label pairs.
/-- The carry is independent of the three alternating sign choices. -/
theorem carry_is_wedge : ∀ mask g h : E,
    CharacterCarryCompletion.carry (ell mask) g h = wedge g h := by
  decide

end D5.S3.VertexAlgebra.FiniteDefectCharacterCarry
