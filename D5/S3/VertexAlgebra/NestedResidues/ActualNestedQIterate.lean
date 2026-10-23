/- GID: D5/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/ActualNestedQIterate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete original scalar nested residue iterate from one Laurent numerator. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor

/-! Signed local-field residue calculus, following Matsuo--Nagatomo and
Bakalov--Kac (math/0402315). Actual field coefficients use Scott Carnahan's
vertexAlg, revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
The iterate compares complete fields against every algebraic dual; its two
support ranges and three independent locality families remain distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators TensorProduct VertexOperator
open D5.S3.VertexAlgebra
namespace D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.FiniteConvolution
open NestedResidues.LatticeHalfFockSliceQuotient
open CollisionRationalExpansions.OrderedRationalExpansion Calculus
local notation "σ" => BinomialKernelDelta.chooseSign
local notation "ε" => StateFieldResidueReconstruction.epsilon

theorem actual_nested_q_iterate
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r : ℤ)
    (n : ℤ) (x : ActualTensor D hu)
    (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ))
            - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (H₁ : ℕ) (H₂ H₃ : ℕ → ℕ)
    (h₁ :
      (FieldNormalProductLocality.deltaEnd ^ H₁)
        (FieldNormalProductLocality.commutator
          (targetSlice D hu (neutralMode D i d a) (gamma + 1))
          (targetSlice D hu b delta)) = 0)
    (h₂ :
      ∀ j ∈ Finset.range ((K : ℤ) - r).toNat,
        (FieldNormalProductLocality.deltaEnd ^ H₂ j)
          (FieldNormalProductLocality.commutator
            (targetCurrent D hu i)
            (qField gamma (r + (j : ℤ)) K
              (targetSlice D hu a gamma)
              (targetSlice D hu b delta))) = 0)
    (h₃ :
      ∀ j ∈ Finset.range (vectorFrequencyBound D b + 1),
        (FieldNormalProductLocality.deltaEnd ^ H₃ j)
          (FieldNormalProductLocality.commutator
            (targetSlice D hu a gamma)
            (qField 1 (j : ℤ) (vectorFrequencyBound D b + 1)
              (targetCurrent D hu i) (targetSlice D hu b delta))) = 0) :
    phi (((qField (gamma + 1) r H₁
      (targetSlice D hu (neutralMode D i d a) (gamma + 1))
      (targetSlice D hu b delta))[[n]]) x) =
      (∑ j ∈ Finset.range ((K : ℤ) - r).toNat,
        σ d j *
          phi (((qField 1 (d - (j : ℤ)) (H₂ j)
            (targetCurrent D hu i)
            (qField gamma (r + (j : ℤ)) K
              (targetSlice D hu a gamma)
              (targetSlice D hu b delta)))[[n]]) x)) -
      ε d • (∑ j ∈ Finset.range (vectorFrequencyBound D b + 1),
        σ d j *
          phi (((qField gamma (d + r - (j : ℤ)) (H₃ j)
            (targetSlice D hu a gamma)
            (qField 1 (j : ℤ) (vectorFrequencyBound D b + 1)
              (targetCurrent D hu i) (targetSlice D hu b delta)))[[n]]) x)) := by
  classical
  let L : ℕ := vectorFrequencyBound D a + 1
  let M : ℕ := vectorFrequencyBound D b + 1
  let degree : ℤ := (L : ℤ) + M + K - d - r - 2
  have current (j : ℕ) :
      targetSlice D hu (neutralMode D i (j : ℤ) b) (delta + 1) =
        qField 1 (j : ℤ) (vectorFrequencyBound D b + 1)
          (targetCurrent D hu i) (targetSlice D hu b delta) := by
    exact native_current_inverse D hu i b delta (j : ℤ)
  have h₃source :
      ∀ j ∈ Finset.range M,
        (FieldNormalProductLocality.deltaEnd ^ H₃ j)
          (FieldNormalProductLocality.commutator
            (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i (j : ℤ) b) (delta + 1))) = 0 := by
    intro j hj
    rw [current j]
    exact h₃ j hj
  have first :=
    NestedResidues.LatticeHalfFockFirstOuterTaylor.fused_weighted_identity
      D hu i a b K gamma delta d r n x phi P coefficients
      H₁ H₂ H₃ h₁ h₂ h₃source
  have middle :=
    NestedResidues.LatticeHalfFockABOuterTaylor.forward_weighted_identity
      D hu i a b K gamma delta d r n x phi P coefficients H₂ h₂
  have third :=
    NestedResidues.LatticeHalfFockSecondSourceTaylor.actual_second_source_third
      D hu i a b K gamma delta d r n x phi P coefficients H₃ h₃source
  simp_rw [← current]
  simp only [smul_eq_mul]
  rw [first, middle, third]
  change
    (∑ u ∈ Finset.range (degree + 1).toNat,
      collisionTaylor P gamma u (degree - u).toNat *
        fusedResidueWeight ((u : ℤ) - M) (d - L)) =
    (∑ u ∈ Finset.range (degree + 1).toNat,
      collisionTaylor P gamma u (degree - u).toNat *
        orderedResidueWeight (d - L) (degree - u + r - K)) -
      ε (d - L) *
        ∑ u ∈ Finset.range (degree + 1).toNat,
          collisionTaylor P gamma u (degree - u).toNat *
            orderedResidueWeight (d - L) ((u : ℤ) - M)
  by_cases negative : degree < 0
  · have empty : (degree + 1).toNat = 0 := by omega
    simp only [empty, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
  · let m : ℕ := degree.toNat
    have hm : (m : ℤ) = degree := by dsimp [m]; omega
    have count : (degree + 1).toNat = m + 1 := by omega
    have index (u : ℕ) : (degree - (u : ℤ)).toNat = m - u := by omega
    have antidiagonal : (m : ℤ) = (L : ℤ) + M + K - d - r - 2 := by
      exact hm
    have balance := finite_collision_balance P gamma d r L M K m antidiagonal
    rw [count]
    simp_rw [index]
    have forward_cast :
        (∑ u ∈ Finset.range (m + 1),
          collisionTaylor P gamma u (m - u) *
            orderedResidueWeight (d - L) (degree - u + r - K)) =
        (∑ u ∈ Finset.range (m + 1),
          collisionTaylor P gamma u (m - u) *
            orderedResidueWeight (d - L) ((m - u : ℕ) + r - K)) := by
      apply Finset.sum_congr rfl
      intro u hu
      have bound : u ≤ m := by simpa using Finset.mem_range.mp hu
      have exponent : degree - (u : ℤ) = ((m - u : ℕ) : ℤ) := by omega
      rw [exponent]
    rw [forward_cast]
    exact balance

end D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
end
