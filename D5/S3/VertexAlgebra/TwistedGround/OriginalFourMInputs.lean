/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous odd polynomial tensors span the original negative-parity carrier. -/

import D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
import Batteries.Tactic.OpenPrivate

/-! Original homogeneous tensor inputs and their finite trilinear expansion. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInputs

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedCoefficients LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeInvolution
open HalfFock.LatticeHalfFockParityField LatticeHalfFockParityT
open private L_zero_of_homogeneous_int from
  D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
open private actualInputBasis actual_input_basis_expansion actual_input_basis_energy from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private oddWeight_sign from D5.S3.VertexAlgebra.LatticeHalfFockParityT
open private negative_support from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

/-- With rank 24, oscillator half-energy H - rank/16 is (2H-3)/2.
The involution is the original polynomial sigma, not a replacement carrier. -/
def CompatiblePolynomial (D : LatticeData) (H : ℕ) (P : Oscillator D) : Prop :=
  sigma D P = -P ∧
    MvPolynomial.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) P (2*(H : ℤ)-3)

/-- Every ground vector is allowed, including zero; no realization premise. -/
def tensorInput (D : LatticeData) (hu : IsUnit D.G.det)
    (P : Oscillator D) (hP : sigma D P = -P) (x : ActualGround D hu) :
    paritySpace D hu (-1) :=
  ⟨P ⊗ₜ[ℂ] x, by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    simp only [actualParity, TensorProduct.map_tmul, LinearMap.id_apply]
    change sigma D P ⊗ₜ[ℂ] x = (-1 : ℂ) • (P ⊗ₜ[ℂ] x)
    rw [hP, TensorProduct.neg_tmul, neg_one_smul]⟩

/-- The actual tensor L0 includes the original rank/16 ground shift. -/
theorem tensor_input_energy (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (P : Oscillator D)
    (hP : CompatiblePolynomial D H P) (x : ActualGround D hu) :
    actualTensorL0 D hu (tensorInput D hu P hP.1 x).val =
      (H : ℂ) • (tensorInput D hu P hP.1 x).val := by
  change tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 0
    (P ⊗ₜ[ℂ] x) = (H : ℂ) • (P ⊗ₜ[ℂ] x)
  simp only [tensorL, tensorEnd, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [L_zero_of_homogeneous_int D (HalfFockSpectralFiberSource.actualInverse D)
    (HalfFockSpectralFiberSource.actualInverse_left D hu)
    (HalfFockSpectralFiberSource.actualInverse_right D hu) P _ hP.2,
    TensorProduct.smul_tmul']
  congr 1
  rw [h24]
  push_cast
  ring

/-- A finite, trilinear expansion in the accepted actual input basis.
This expands inputs, independently of any detector argument. -/
theorem input_trilinear_expansion (D : LatticeData) (hu : IsUnit D.G.det)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ] V) (u v w : paritySpace D hu (-1)) :
    F u v w =
      ∑ i ∈ ((actualAmbientBasis D hu).repr u.val).support.attach,
      ∑ j ∈ ((actualAmbientBasis D hu).repr v.val).support.attach,
      ∑ k ∈ ((actualAmbientBasis D hu).repr w.val).support.attach,
        (((actualAmbientBasis D hu).repr u.val i.val) *
          ((actualAmbientBasis D hu).repr v.val j.val) *
          ((actualAmbientBasis D hu).repr w.val k.val)) •
            F (actualInputBasis D hu u i) (actualInputBasis D hu v j)
              (actualInputBasis D hu w k) := by
  conv_lhs => rw [← actual_input_basis_expansion D hu u]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs => rw [← actual_input_basis_expansion D hu v]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  conv_lhs => rw [← actual_input_basis_expansion D hu w]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, mul_assoc]

private theorem basis_compatible (D : LatticeData) (hu : IsUnit D.G.det)
    (u : paritySpace D hu (-1))
    (i : {i : OddMonomial D × LatticeTwistedGroundRealization.Half (groundRank D hu) //
      i ∈ ((actualAmbientBasis D hu).repr u.val).support}) :
    CompatiblePolynomial D ((oddWeight D i.val.1+3)/2)
      (MvPolynomial.monomial i.val.1 1) := by
  have odd := negative_support D hu u i.val i.property
  constructor
  · rw [sigma_monomial, ← oddWeight_sign, neg_one_pow_eq_pow_mod_two, odd]
    simp
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    have cast_weight : Finsupp.weight (fun k => (omega D k : ℤ)) i.val.1 =
        (oddWeight D i.val.1 : ℤ) := by
      simp only [oddWeight, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
        Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
    rw [cast_weight]
    omega

/-- Checking a trilinear law on compatible homogeneous polynomial tensors
suffices for all original M inputs. The actual finite basis expansion and its
accepted energy theorem, rather than a new realization assumption, supply the
homogeneous tensor tests. -/
theorem input_trilinear_ext (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : paritySpace D hu (-1) →ₗ[ℂ] paritySpace D hu (-1) →ₗ[ℂ]
      paritySpace D hu (-1) →ₗ[ℂ] V)
    (hF : ∀ (H K L : ℕ) (P Q R : Oscillator D)
      (hP : CompatiblePolynomial D H P) (hQ : CompatiblePolynomial D K Q)
      (hR : CompatiblePolynomial D L R)
      (x y z : ActualGround D hu),
      actualTensorL0 D hu (tensorInput D hu P hP.1 x).val =
        (H : ℂ) • (tensorInput D hu P hP.1 x).val →
      actualTensorL0 D hu (tensorInput D hu Q hQ.1 y).val =
        (K : ℂ) • (tensorInput D hu Q hQ.1 y).val →
      actualTensorL0 D hu (tensorInput D hu R hR.1 z).val =
        (L : ℂ) • (tensorInput D hu R hR.1 z).val →
      F (tensorInput D hu P hP.1 x) (tensorInput D hu Q hQ.1 y)
        (tensorInput D hu R hR.1 z) = 0) :
    ∀ u v w : paritySpace D hu (-1), F u v w = 0 := by
  intro u v w
  rw [input_trilinear_expansion]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  have ei := actual_input_basis_energy D hu h24 u i
  have ej := actual_input_basis_energy D hu h24 v j
  have ek := actual_input_basis_energy D hu h24 w k
  have qi := basis_compatible D hu u i
  have qj := basis_compatible D hu v j
  have qk := basis_compatible D hu w k
  have bi : actualInputBasis D hu u i = tensorInput D hu
      (MvPolynomial.monomial i.val.1 1) qi.1 (Pi.single i.val.2 1) := by
    apply Subtype.ext
    exact actual_basis_apply D hu i.val.1 i.val.2
  have bj : actualInputBasis D hu v j = tensorInput D hu
      (MvPolynomial.monomial j.val.1 1) qj.1 (Pi.single j.val.2 1) := by
    apply Subtype.ext
    exact actual_basis_apply D hu j.val.1 j.val.2
  have bk : actualInputBasis D hu w k = tensorInput D hu
      (MvPolynomial.monomial k.val.1 1) qk.1 (Pi.single k.val.2 1) := by
    apply Subtype.ext
    exact actual_basis_apply D hu k.val.1 k.val.2
  rw [bi] at ei
  rw [bj] at ej
  rw [bk] at ek
  rw [bi, bj, bk, hF _ _ _ _ _ _ qi qj qk _ _ _ ei ej ek, smul_zero]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInputs
