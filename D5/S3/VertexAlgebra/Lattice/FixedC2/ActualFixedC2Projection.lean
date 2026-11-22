/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2Projection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Linear projection to the actual fixed carrier and its parity evaluation. -/

import D5.S3.VertexAlgebra.LatticeInvolution

/-! The fixed-space projection for the sign involution, realized by `plusPart`. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeInvolution

open LatticeGeneratingFieldLocality

noncomputable section

local instance projectionFixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

private theorem half_add_self (D : LatticeData) (v : Carrier D) :
    (2 : ℂ)⁻¹ • (v + v) = v := by
  rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]

private theorem theta_twice (D : LatticeData) (v : Carrier D) :
    theta D (theta D v) = v :=
  theta_involutive D v

private theorem plus_mem (D : LatticeData) (v : Carrier D) :
    plusPart D v ∈ fixedSpace D := by
  simp only [mem_fixedSpace, plusPart, map_smul, map_add, theta_twice]
  rw [add_comm (theta D v) v]

/-- Complex-linear projection onto the fixed carrier, with value given by `plusPart`. -/
def plusProjection (D : LatticeData) : Carrier D →ₗ[ℂ] FixedCarrier D where
  toFun v := ⟨plusPart D v, plus_mem D v⟩
  map_add' a b := Subtype.ext (by
    change plusPart D (a + b) = plusPart D a + plusPart D b
    simp only [plusPart, map_add, smul_add]
    abel)
  map_smul' c a := Subtype.ext (by
    change plusPart D (c • a) = c • plusPart D a
    simp only [plusPart, map_smul, ← smul_add]
    rw [smul_comm])

/-- The projection is the identity on fixed states. -/
theorem plusProjection_fixed (D : LatticeData) (v : FixedCarrier D) :
    plusProjection D v.val = v := by
  apply Subtype.ext
  change plusPart D v.val = v.val
  rw [plusPart, (mem_fixedSpace D _).mp v.property, half_add_self]

/-- The projection kills anti-invariant states. -/
theorem plusProjection_odd (D : LatticeData) (v : Carrier D)
    (h : theta D v = -v) : plusProjection D v = 0 := by
  apply Subtype.ext
  change plusPart D v = 0
  simp [plusPart, h]

end

end D5.S3.VertexAlgebra.LatticeInvolution
