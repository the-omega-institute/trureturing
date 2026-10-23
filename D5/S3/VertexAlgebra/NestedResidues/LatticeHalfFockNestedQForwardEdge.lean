/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockNestedQForwardEdge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockNestedQForwardEdge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact forward nested-Q collision equality on the empty inner-cutoff branch. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOuterTaylorEvaluation

/-! Exact empty-cutoff branch of the actual forward nested-Q Taylor identity. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockOuterTaylorEvaluation
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents
open CollisionRationalExpansions.OrderedRationalExpansion
open scoped BigOperators VertexOperator
noncomputable section

/-- When the supplied inner cutoff is at most the signed inner lift, the
forward component of the actual nested-Q telescope is an empty finite sum.
The right hand Taylor side is empty for the same reason: every admissible
Taylor index has nonnegative ordered-residue argument. This is the exact
arbitrary-input equality on that branch; no locality cutoff is transferred to
an individual Laurent monomial. -/
theorem forward_weighted_identity_of_cutoff_le_lift
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3) (H₂ : ℕ → ℕ)
    (hKr : (K : ℤ) ≤ r) :
    (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
      BinomialKernelDelta.chooseSign d j *
        phi (((qField 1 (d - j) (H₂ j) (targetCurrent D hu i)
          (qField gamma (r + j) K
            (targetSlice D hu a gamma)
            (targetSlice D hu b delta)))[[n]]) x)) =
      (∑ u ∈ Finset.range
          ((vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K - d - r - 2 + 1).toNat),
        collisionTaylor P gamma u
            ((vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K - d - r - 2 - u).toNat) *
          orderedResidueWeight (d - (vectorFrequencyBound D a + 1))
            (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) + K - d - r - 2 - u + r - K)) := by
  have empty_inner : ((K : ℤ) - r).toNat = 0 := by omega
  rw [empty_inner]
  simp only [Finset.range_zero, Finset.sum_empty]
  let degree : ℤ :=
    (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2
  change 0 =
    (∑ u ∈ Finset.range (degree + 1).toNat,
      collisionTaylor P gamma u (degree - u).toNat *
        orderedResidueWeight (d - (vectorFrequencyBound D a + 1))
          (degree - u + r - K))
  by_cases negative : degree < 0
  · have empty_degree : (degree + 1).toNat = 0 := by omega
    simp only [empty_degree, Finset.range_zero, Finset.sum_empty]
  · have nonnegative : 0 ≤ degree := by omega
    symm
    apply Finset.sum_eq_zero
    intro u hu
    have u_le : u ≤ degree := by
      have := Finset.mem_range.mp hu
      omega
    have u_le_int : (u : ℤ) ≤ degree := by omega
    have degree_sub_nonnegative : 0 ≤ degree - (u : ℤ) := by omega
    have residual_nonnegative : 0 ≤ degree - (u : ℤ) + r - K := by
      omega
    unfold orderedResidueWeight
    rw [if_neg (not_lt_of_ge residual_nonnegative)]
    simp

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge
