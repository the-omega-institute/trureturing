/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual complete binary Taylor evaluation at independent outer locality orders. -/

import D5.S3.VertexAlgebra.NestedResidues.BinaryLaurentEvaluation
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge

/-! The binary Laurent numerator belongs to the original complete G.
The actual inner cutoff K and the independent complete-field locality
orders H(j) are preserved. Its conversion to collisionTaylor P gamma
on nonnegative degrees remains a separate obligation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockABLocalResidue LatticeHalfFockABActualReadout BinaryLaurentEvaluation
open LatticeHalfFockClearedTaylorReadout UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator
noncomputable section

/- proof_shape: actual_ab_binary_taylor: content
   admission_basis: escape-witness
   escape_witness: Genuine complete-field locality pads the actual outer
   readout to max(H(j),B(j)); the generic signed Laurent evaluation then
   contracts the complete fractional sum. The original inner K is unchanged.
   consumer: forward_weighted_identity_of_negative_degree -/
set_option maxHeartbeats 1600000 in
/-- The actual middle family is evaluated using a finite Laurent numerator
of its own complete binary G. Every independent H(j) is preserved through
complete-field support, without locality on a monomial or an ordered half. -/
theorem actual_ab_binary_taylor
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0) :
    let B := fun j : ℕ => vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
      ((K : ℤ) - (r + j) - 1).toNat
    ∃ Q : ℕ → BinaryPolynomial, ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      binaryRational (Q j) (-(B j : ℤ)) =
        completeAB gamma (r + j) K (originalRational D a b K P) ∧
      phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
        (qField gamma (r + j) K (targetSlice D hu a gamma)
          (targetSlice D hu b delta)))[[n]]) x) =
        binaryTaylor (Q j) (B j) 1 (d - j) n := by
  classical
  dsimp only
  let B := fun j : ℕ => vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
    ((K : ℤ) - (r + j) - 1).toNat
  choose Q hQ using (fun j : ℕ => ab_complete_pole_bound D a b K K P gamma (r + j))
  refine ⟨Q, ?_⟩
  intro j hj
  have representation : binaryRational (Q j) (-(B j : ℤ)) =
      completeAB gamma (r + j) K (originalRational D a b K P) := by
    rw [hQ j]
    simp only [binaryRational, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rfl
  refine ⟨representation, ?_⟩
  let G := completeAB gamma (r + j) K (originalRational D a b K P)
  have forward :
      (fun k l => lastSourceLocalQ 1 true gamma (r + j) K l k
        (originalRational D a b K P)) = binaryModes false G := by
    funext k l
    exact (ab_complete_remaining_orders D a b K K P gamma (r + j) l k).2.2.1
  have backward :
      (fun k l => lastSourceLocalQ 1 false gamma (r + j) K k l
        (originalRational D a b K P)) = binaryModes true G := by
    funext k l
    exact (ab_complete_remaining_orders D a b K K P gamma (r + j) k l).2.2.2
  have completion := (actual_ab_joint_outer_support D hu i a b K gamma delta d r n
    x phi P coefficients H locality).1 j hj
  change OuterQCompletion 1 (d - j) n (H j)
    (fun k l => lastSourceLocalQ 1 true gamma (r + j) K l k
      (originalRational D a b K P))
    (fun k l => lastSourceLocalQ 1 false gamma (r + j) K k l
      (originalRational D a b K P)) at completion
  rw [forward, backward] at completion
  have actual := (actual_ab_nested_readout D hu i a b K K (H j)
    gamma delta d r n j x phi P coefficients).2.2
  change phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
      (qField gamma (r + j) K (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
    supportedQReadout 1 (d - j) (H j) n (binaryModes false G) (binaryModes true G) at actual
  have pad := (completion.2 (H j) le_rfl).trans
    (completion.2 (max (B j) (H j)) (Nat.le_max_right _ _)).symm
  rw [actual, pad]
  change binaryRational (Q j) (-(B j : ℤ)) = G at representation
  rw [← representation]
  exact binary_fractional_taylor (Q j) (B j) (max (B j) (H j)) 1 (d - j) n
    (Nat.le_max_left _ _)

/- proof_shape: forward_weighted_identity_of_negative_degree: content
   admission_basis: escape-witness
   escape_witness: On j<N the signed binary Taylor order B(j)-(d-j)-1
   equals the original degree L+M+K-d-r-2. Negative degree annihilates
   each complete actual nested coefficient and the original Taylor sum. -/
set_option maxHeartbeats 1600000 in
/-- The original middle equality on every negative Taylor degree, retaining
its full actual homogeneous numerator and independent outer-locality family. -/
theorem forward_weighted_identity_of_negative_degree
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H : ℕ → ℕ)
    (locality : ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))) = 0)
    (negative : (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + (K : ℤ) - d - r - 2 < 0) :
    let degree : ℤ := (vectorFrequencyBound D a + 1 : ℕ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2
    (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
      BinomialKernelDelta.chooseSign d j *
        phi (((qField 1 (d - j) (H j) (targetCurrent D hu i)
          (qField gamma (r + j) K (targetSlice D hu a gamma)
            (targetSlice D hu b delta)))[[n]]) x)) =
      ∑ u ∈ Finset.range (degree + 1).toNat,
        collisionTaylor P gamma u (degree - u).toNat *
          orderedResidueWeight (d - (vectorFrequencyBound D a + 1 : ℕ))
            (degree - u + r - K) := by
  classical
  dsimp only
  rw [show (((vectorFrequencyBound D a + 1 : ℕ) : ℤ) +
      (vectorFrequencyBound D b + 1 : ℕ) + K - d - r - 2 + 1).toNat = 0 by omega]
  simp only [Finset.range_zero, Finset.sum_empty]
  obtain ⟨Q, evaluation⟩ := actual_ab_binary_taylor D hu i a b K gamma delta d r n
    x phi P coefficients H locality
  apply Finset.sum_eq_zero
  intro j hj
  rw [(evaluation j hj).2]
  have inside := Finset.mem_range.mp hj
  have low : 0 ≤ (K : ℤ) - (r + j) - 1 := by omega
  have high : ¬ d - (j : ℤ) <
      (vectorFrequencyBound D a + 1 + (vectorFrequencyBound D b + 1) +
        ((K : ℤ) - (r + j) - 1).toNat : ℕ) := by omega
  rw [binaryTaylor, ite_eq_right high, mul_zero]

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
