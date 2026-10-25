/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-numerator actual nested-current iterate identity with independent locality orders. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockFirstOuterTaylor
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABOuterTaylor
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The original three Taylor contractions are joined on the same actual
numerator. Source/source locality is supplied at the numerator's own cutoff;
no locality of a monomial or either ordered half is inferred.
Classical formal local-field calculus: Matsuo--Nagatomo and Bakalov--Kac,
math/0402315. Signed binomial and dual-separation infrastructure: Mathlib,
Apache 2.0. No literature novelty or completed string model is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockClearedTaylorReadout
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open UniformGradedLocalCorrelator
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open scoped BigOperators VertexOperator
noncomputable section

private theorem residue_weight_cancellation (A k : ℤ) :
    fusedResidueWeight A k =
      orderedResidueWeight k (-A-k-2) -
        StateFieldResidueReconstruction.epsilon k * orderedResidueWeight k A := by
  by_cases negative : k < 0
  · let t := (-k-1).toNat
    have kt : -(t : ℤ)-1 = k := by dsimp [t]; omega
    have first : (-A-k-2 < 0) ↔ 0 ≤ A-t := by omega
    have second : (A < 0) ↔ 0 ≤ -A-1 := by omega
    have index : (-(-A-k-2)-1).toNat = (A-t).toNat := by omega
    have h := signed_kernel_choose t A
    rw [kt] at h
    simpa only [fusedResidueWeight, if_pos negative, orderedResidueWeight,
      first, second, index] using h.symm
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
    rw [fusedResidueWeight, if_neg (by omega)]
    unfold orderedResidueWeight
    by_cases left : -A-(N : ℤ)-2 < 0
    · by_cases right : A < 0
      · rw [if_pos left, if_pos right]
        let p := (-(-A-(N : ℤ)-2)-1).toNat
        let q := (-A-1).toNat
        have total : p+q = N := by dsimp [p,q]; omega
        have choose : N.choose p = N.choose q :=
          Nat.choose_symm_of_eq_add total.symm
        have sign : (-1 : ℂ)^p = (-1 : ℂ)^N * (-1 : ℂ)^q := by
          rw [← total, pow_add, mul_assoc, ← mul_pow]
          norm_num
        simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast,
          Int.cast_natCast, StateFieldResidueReconstruction.epsilon, zpow_natCast]
        change 0 = (-1 : ℂ)^p * (N.choose p : ℂ) -
          (-1 : ℂ)^N * ((-1 : ℂ)^q * (N.choose q : ℂ))
        rw [sign, choose]
        ring
      · rw [if_pos left, if_neg right]
        have high : N < (-(-A-(N : ℤ)-2)-1).toNat := by omega
        simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast,
          Int.cast_natCast, Nat.choose_eq_zero_of_lt high, Nat.cast_zero, Int.cast_zero,
          mul_zero, sub_zero]
    · rw [if_neg left]
      by_cases right : A < 0
      · rw [if_pos right]
        have high : N < (-A-1).toNat := by omega
        simp only [BinomialKernelDelta.chooseSign, Ring.choose_natCast,
          Int.cast_natCast, Nat.choose_eq_zero_of_lt high, Nat.cast_zero, Int.cast_zero,
          mul_zero, sub_zero]
      · rw [if_neg right]
        ring

/-- A finite scalar numerator at the very cutoff witnessing actual A/B
locality. The same actual JAB array supplies every signed homogeneous slice. -/
private theorem local_numerator
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta : ℤ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ) (total : ℤ) :
    ∃ P : LabelledPolynomial ℂ 3, ∀ e : Exponent 3,
      P.coeff e = if totalExponent e = total then
        phi (actualNumerator D hu i a b gamma delta K x e) else 0 := by
  have pairLocal : ∀ first second : Fin 3, first < second →
      (FieldNormalProductLocality.deltaEnd ^ threeOrders D a b K (first, second))
        (FieldNormalProductLocality.commutator
          (threeFields D hu i a b gamma delta first)
          (threeFields D hu i a b gamma delta second)) = 0 := by
    intro first second less
    fin_cases first <;> fin_cases second <;> norm_num at less
    · exact current_slice_locality D hu i a gamma
    · exact current_slice_locality D hu i b delta
    · exact locality
  have finite := (common_cleared_fields
    (threeFields D hu i a b gamma delta) x 1 (threeOrders D a b K)
    pairLocal [0,1,2] (by decide) (by intro label; fin_cases label <;> simp)).2.2 total
  let F : Distribution 3 ℂ :=
    fun e => phi (actualNumerator D hu i a b gamma delta K x e)
  have scalarFinite : {e : Exponent 3 | totalExponent e = total ∧ F e ≠ 0}.Finite := by
    apply finite.subset
    intro e he
    refine ⟨he.1, ?_⟩
    intro hz
    exact he.2 (by simp [F, actualNumerator, hz])
  exact ⟨slicePolynomial F total scalarFinite,
    fun e => slicePolynomial_coeff F total scalarFinite e⟩

/- proof_shape: actual_nested_iterate: content
   admission_basis: escape-witness
   escape_witness: The complete signed two-order residue cancellation is
   contracted against the same actual homogeneous numerator, then all linear
   functionals separate the native nested iterate. The source/source locality
   witness belongs to that exact numerator cutoff. -/
/-- Actual nested iterate equality with independent whole-field localities.
All lifts and modes are signed. The two finite ranges are exactly K-r and
the original second source's current bound. -/
theorem actual_nested_iterate
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K : ℕ) (gamma delta d r : ℤ)
    (H₁ : ℕ) (H₂ H₃ : ℕ → ℕ)
    (localityAB : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu a gamma) (targetSlice D hu b delta)) = 0)
    (locality₁ : (FieldNormalProductLocality.deltaEnd ^ H₁)
      (FieldNormalProductLocality.commutator
        (targetSlice D hu (neutralMode D i d a) (gamma+1))
        (targetSlice D hu b delta)) = 0)
    (locality₂ : ∀ j ∈ Finset.range ((K : ℤ)-r).toNat,
      (FieldNormalProductLocality.deltaEnd ^ H₂ j)
        (FieldNormalProductLocality.commutator (targetCurrent D hu i)
          (qField gamma (r+j) K
            (targetSlice D hu a gamma) (targetSlice D hu b delta))) = 0)
    (locality₃ : ∀ j ∈ Finset.range (vectorFrequencyBound D b+1),
      (FieldNormalProductLocality.deltaEnd ^ H₃ j)
        (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta+1))) = 0) :
    qField (gamma+1) r H₁
        (targetSlice D hu (neutralMode D i d a) (gamma+1))
        (targetSlice D hu b delta) =
      (∑ j ∈ Finset.range ((K : ℤ)-r).toNat,
        BinomialKernelDelta.chooseSign d j •
          qField 1 (d-j) (H₂ j) (targetCurrent D hu i)
            (qField gamma (r+j) K
              (targetSlice D hu a gamma) (targetSlice D hu b delta))) -
      StateFieldResidueReconstruction.epsilon d •
        ∑ j ∈ Finset.range (vectorFrequencyBound D b+1),
          BinomialKernelDelta.chooseSign d j •
            qField gamma (d+r-j) (H₃ j) (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta+1)) := by
  classical
  apply HVertexOperator.coeff_inj
  funext e
  simp only [VertexOperator.coeff_eq_ncoeff]
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro phi
  rw [map_sub]
  apply sub_eq_zero.mpr
  let n : ℤ := -e-1
  let L : ℤ := vectorFrequencyBound D a+1
  let M : ℤ := vectorFrequencyBound D b+1
  let degree : ℤ := L+M+K-d-r-2
  obtain ⟨P, coefficients⟩ := local_numerator D hu i a b K gamma delta localityAB x phi
    ((∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ))-d-r-n-3)
  have first := LatticeHalfFockFirstOuterTaylor.fused_weighted_identity
    D hu i a b K gamma delta d r n x phi P coefficients H₁ H₂ H₃
    locality₁ locality₂ locality₃
  have middle := LatticeHalfFockABOuterTaylor.forward_weighted_identity
    D hu i a b K gamma delta d r n x phi P coefficients H₂ locality₂
  have last := LatticeHalfFockSecondSourceTaylor.actual_second_source_third
    D hu i a b K gamma delta d r n x phi P coefficients H₃ locality₃
  dsimp only at first middle last
  simp only [Nat.cast_add, Nat.cast_one] at first middle last
  have weights (u : ℕ) :
      fusedResidueWeight ((u : ℤ)-M) (d-L) =
        orderedResidueWeight (d-L) (degree-u+r-K) -
          StateFieldResidueReconstruction.epsilon (d-L) *
            orderedResidueWeight (d-L) ((u : ℤ)-M) := by
    have h := residue_weight_cancellation ((u : ℤ)-M) (d-L)
    have index : -((u : ℤ)-M)-(d-L)-2 = degree-u+r-K := by dsimp [degree]; ring
    rwa [index] at h
  have contraction :
      (∑ u ∈ Finset.range (degree+1).toNat,
        collisionTaylor P gamma u (degree-u).toNat *
          fusedResidueWeight ((u : ℤ)-M) (d-L)) =
      (∑ u ∈ Finset.range (degree+1).toNat,
        collisionTaylor P gamma u (degree-u).toNat *
          orderedResidueWeight (d-L) (degree-u+r-K)) -
      StateFieldResidueReconstruction.epsilon (d-L) *
        ∑ u ∈ Finset.range (degree+1).toNat,
          collisionTaylor P gamma u (degree-u).toNat *
            orderedResidueWeight (d-L) ((u : ℤ)-M) := by
    simp_rw [weights, mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    ring
  have scalar :
      phi (((qField (gamma+1) r H₁
        (targetSlice D hu (neutralMode D i d a) (gamma+1))
        (targetSlice D hu b delta))[[n]]) x) =
      (∑ j ∈ Finset.range ((K : ℤ)-r).toNat,
        BinomialKernelDelta.chooseSign d j *
          phi (((qField 1 (d-j) (H₂ j) (targetCurrent D hu i)
            (qField gamma (r+j) K
              (targetSlice D hu a gamma) (targetSlice D hu b delta)))[[n]]) x)) -
      StateFieldResidueReconstruction.epsilon d *
        ∑ j ∈ Finset.range (vectorFrequencyBound D b+1),
          BinomialKernelDelta.chooseSign d j *
            phi (((qField gamma (d+r-j) (H₃ j) (targetSlice D hu a gamma)
              (targetSlice D hu (neutralMode D i j b) (delta+1)))[[n]]) x) :=
    first.trans (contraction.trans (by rw [← middle, ← last]))
  simpa only [n, L, M, degree, map_sum, map_smul, map_sub,
    Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, LinearMap.sub_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using scalar

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi
