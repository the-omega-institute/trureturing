/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldFaithfulness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original twisted vacuum coefficient and faithful fixed-sector action. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSourceModeTransport

/-! The weight-two twisted pairing supplies the fixed vacuum in mode three.
The original mixed Jacobi law then detects every fixed state. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

open LatticeGeneratingFieldLocality LatticeInvolution
open HalfFock.LatticeHalfFockParityField
open OriginalFourMChargeCoset (originalI originalI_three_eq_vacuum_smul)

/-- The literal original mode `I₃` takes a pair of actual negative twisted
states to the fixed vacuum for every supported rank-24 lattice. -/
theorem originalI_three_eq_vacuum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24) :
    ∃ u v : paritySpace D hu (-1), originalI D hu hD 3 u v = fixedVacuum D := by
  obtain ⟨a, u, v, ha, huH, hvK, _, hne⟩ :=
    weight_two_normalized_vacuum_witness D hu h24 hD
  refine ⟨u, (normalizedCoefficient D hu 3 u v 0 a)⁻¹ • v, ?_⟩
  rw [map_smul, originalI_three_eq_vacuum_smul D hu hD h24 u v huH hvK a ha,
    smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The original fixed-sector field is faithful on the actual negative
twisted sector when all its integer modes are tested. -/
theorem fixedParitySlice_faithful (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (a : FixedCarrier D)
    (ha : ∀ (n : ℤ) (w : paritySpace D hu (-1)),
      ((fixedParitySlice D hu (-1) a)[[n]]) w = 0) : a = 0 := by
  obtain ⟨u, v, hvac⟩ := originalI_three_eq_vacuum D hu hD h24
  have h := original_mixed_jacobi D hu hD h24 (-1) 3 0 a u v
  simp only [ha, map_zero, LinearMap.zero_apply, smul_zero, finsum_zero, sub_zero] at h
  rw [finsum_eq_single _ 0] at h
  · have hcreate := fixed_creation D a
    change fixedMode D a (-1) (fixedVacuum D) = a at hcreate
    simpa only [Nat.cast_zero, add_zero, sub_zero, Int.cast_zero, pow_zero,
      Ring.choose_zero_right, mul_one, one_smul, hvac, hcreate] using h.symm
  · intro j hj
    simp only [Int.cast_zero, Ring.choose_zero_pos ℂ (Nat.pos_of_ne_zero hj), mul_zero, zero_smul]

end D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
