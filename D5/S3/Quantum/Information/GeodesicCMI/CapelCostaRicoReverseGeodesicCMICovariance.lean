/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product-unitary covariance transports the reverse CMI witness to every faithful qubit reference. -/

import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
import D5.S3.Quantum.Information.PartialTrace.Isometries
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Unitary covariance of Capel and Costa-Rico's reverse geodesic CMI
(arXiv:2608.15833v1, equations (52), (59), (62), (63), (357)).
For Open Question 6, the released diagonal counterexample transports to the
standard coordinates of each fixed faithful qubit reference. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI

open Matrix Filter Set
open scoped BigOperators ComplexOrder CStarAlgebra Kronecker Matrix MatrixOrder
  Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceDistance traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
  (unitaryConjugateState)
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance (partialTrace_isometries)
open D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability (traceNorm_isometry)

noncomputable section

section Unitary

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Conjugation on matrices in the specified orthonormal coordinates. -/
abbrev conjugation (U : unitaryGroup n ℂ) : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ U

/-- Tensor product of unitaries in the product basis. -/
def tensorUnitary (U : unitaryGroup n ℂ) (V : unitaryGroup m ℂ) :
    unitaryGroup (n × m) ℂ :=
  ⟨U.val ⊗ₖ V.val, Matrix.kronecker_mem_unitary U.property V.property⟩

private theorem conjugation_apply (U : unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    conjugation U X = U.val * X * U.valᴴ := rfl

private theorem conjugation_tensor (U : unitaryGroup n ℂ) (V : unitaryGroup m ℂ)
    (X : Matrix n n ℂ) (Y : Matrix m m ℂ) :
    conjugation (tensorUnitary U V) (X ⊗ₖ Y) =
      conjugation U X ⊗ₖ conjugation V Y := by
  simp only [conjugation_apply]
  change (U.val ⊗ₖ V.val) * (X ⊗ₖ Y) * (U.val ⊗ₖ V.val)ᴴ = _
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

private theorem cfc_conjugation (U : unitaryGroup n ℂ)
    (f : ℝ → ℝ) (X : Matrix n n ℂ) :
    cfc f (conjugation U X) = conjugation U (cfc f X) := by
  by_cases hX : IsSelfAdjoint X
  · exact (StarAlgHomClass.map_cfc (conjugation U) f X
      (X.finite_real_spectrum.continuousOn f)
      (StarAlgEquiv.isometry (conjugation U)).continuous hX (hX.map (conjugation U))).symm
  · have hUX : ¬ IsSelfAdjoint (conjugation U X) := by
      intro h
      exact hX (by simpa only [StarAlgEquiv.symm_apply_apply] using h.map (conjugation U).symm)
    rw [cfc_apply_of_not_predicate _ hUX, cfc_apply_of_not_predicate _ hX, map_zero]

/-- Conjugation of a density state, expressed in the same matrix coordinates. -/
abbrev conjugateDensity (U : unitaryGroup n ℂ) (ρ : DensityState n) : DensityState n :=
  unitaryConjugateState U.val U.property ρ

theorem toMatrix_conjugateDensity (U : unitaryGroup n ℂ) (ρ : DensityState n) :
    toMatrix (conjugateDensity U ρ) = conjugation U (toMatrix ρ) := rfl

theorem traceDistance_conjugateDensity (U : unitaryGroup n ℂ) (ρ σ : DensityState n) :
    traceDistance (conjugateDensity U ρ) (conjugateDensity U σ) = traceDistance ρ σ := by
  change traceNorm (toMatrix (conjugateDensity U ρ) -
      toMatrix (conjugateDensity U σ)) / 2 = traceNorm (toMatrix ρ - toMatrix σ) / 2
  rw [toMatrix_conjugateDensity, toMatrix_conjugateDensity, ← map_sub, conjugation_apply,
    traceNorm_isometry U.val (Unitary.coe_star_mul_self U)]

end Unitary

section GeodesicCovariance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unitary for Hilbert–Schmidt conjugation in the release's row-first
matrix-unit coordinates. -/
def hilbertSchmidtUnitary (U : unitaryGroup n ℂ) : unitaryGroup (n × n) ℂ :=
  tensorUnitary U (Matrix.UnitaryGroup.transpose (star U))

private theorem hilbertSchmidtUnitary_val (U : unitaryGroup n ℂ) :
    (hilbertSchmidtUnitary U).val = U.val ⊗ₖ (U.valᴴ)ᵀ := rfl

private theorem hilbertSchmidtUnitary_adjoint (U : unitaryGroup n ℂ) :
    (hilbertSchmidtUnitary U).valᴴ = U.valᴴ ⊗ₖ U.valᵀ := by
  rw [hilbertSchmidtUnitary_val, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

/-- Equation (52) is conjugated by the unitary induced on matrix units. -/
theorem geodesicModular_conjugation (U : unitaryGroup n ℂ) (t : ℝ)
    (r s : Matrix n n ℂ) :
    geodesicModular t (conjugation U r) (conjugation U s) =
      conjugation (hilbertSchmidtUnitary U) (geodesicModular t r s) := by
  simp only [geodesicModular_eq_kronecker, cfc_conjugation, ← map_mul (conjugation U)]
  rw [conjugation_apply (hilbertSchmidtUnitary U), hilbertSchmidtUnitary_adjoint,
    hilbertSchmidtUnitary_val, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [conjugation_apply, Matrix.transpose_mul, Matrix.mul_assoc]

private theorem weightedVector_conjugation (U : unitaryGroup n ℂ) (s : Matrix n n ℂ) :
    weightedVector (conjugation U s) = (hilbertSchmidtUnitary U).val *ᵥ weightedVector s := by
  change (fun i : n × n => cfc Real.sqrt (conjugation U s) i.1 i.2) = _
  rw [cfc_conjugation, conjugation_apply, hilbertSchmidtUnitary_val]
  change (U.val * cfc Real.sqrt s * U.valᴴ)ᵀ.vec =
    (U.val ⊗ₖ (U.valᴴ)ᵀ) *ᵥ (cfc Real.sqrt s)ᵀ.vec
  simp only [Matrix.kronecker_mulVec_vec, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Equation (59) is unchanged by simultaneous unitary conjugation of both inputs. -/
theorem geodesicRelativeEntropy_conjugation (U : unitaryGroup n ℂ) (t : ℝ)
    (r s : Matrix n n ℂ) :
    geodesicRelativeEntropy t (conjugation U r) (conjugation U s) =
      geodesicRelativeEntropy t r s := by
  let W := hilbertSchmidtUnitary U
  have hW : W.valᴴ * W.val = 1 := Unitary.coe_star_mul_self W
  have hinner (x y : n × n → ℂ) :
      star (W.val *ᵥ x) ⬝ᵥ (W.val *ᵥ y) = star x ⬝ᵥ y := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hW,
      Matrix.vecMul_one]
  unfold geodesicRelativeEntropy
  rw [geodesicModular_conjugation, cfc_conjugation, weightedVector_conjugation,
    conjugation_apply]
  change (star (W.val *ᵥ weightedVector s) ⬝ᵥ
    ((W.val * cfc (fun z : ℝ => z * Real.log z) (geodesicModular t r s) * W.valᴴ) *ᵥ
      (W.val *ᵥ weightedVector s))).re = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ W.valᴴ W.val, hW, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hinner]

end GeodesicCovariance

section ProductCovariance

private theorem partialTraceRight_conjugation
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : unitaryGroup A ℂ) (V : unitaryGroup B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (conjugation (tensorUnitary U V) X) =
      conjugation U (partialTraceRight X) :=
  partialTrace_isometries U.val V.val (Unitary.coe_star_mul_self V) X

private theorem partialTraceLeft_conjugation
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : unitaryGroup A ℂ) (V : unitaryGroup B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (conjugation (tensorUnitary U V) X) =
      conjugation V (partialTraceLeft X) := by
  let e := Equiv.prodComm B A
  have hs (M : Matrix (A × B) (A × B) ℂ) :
      partialTraceLeft M = partialTraceRight (M.submatrix e e) := rfl
  rw [conjugation_apply, conjugation_apply, hs, hs]
  change partialTraceRight (((U.val ⊗ₖ V.val) * X * (U.val ⊗ₖ V.val)ᴴ).submatrix e e) = _
  have ht : ((U.val ⊗ₖ V.val) * X * (U.val ⊗ₖ V.val)ᴴ).submatrix e e =
      (V.val ⊗ₖ U.val) * X.submatrix e e * (V.val ⊗ₖ U.val)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e]
    have hk : (U.val ⊗ₖ V.val).submatrix e e = V.val ⊗ₖ U.val := by
      ext i j
      simp [e, mul_comm]
    rw [hk, ← Matrix.conjTranspose_submatrix, hk]
  rw [ht]
  exact partialTrace_isometries V.val U.val (Unitary.coe_star_mul_self U) (X.submatrix e e)

private theorem submatrix_conjugation {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : B ≃ A) (U : unitaryGroup A ℂ) (V : unitaryGroup B ℂ)
    (h : U.val.submatrix e e = V.val) (X : Matrix A A ℂ) :
    (conjugation U X).submatrix e e = conjugation V (X.submatrix e e) := by
  simp only [conjugation_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
    ← Matrix.conjTranspose_submatrix, h]

theorem marginalAB_conjugation (U V W : unitaryGroup Bit ℂ) (X : Matrix Triple Triple ℂ) :
    marginalAB (conjugation (tensorUnitary (tensorUnitary U V) W) X) =
      conjugation (tensorUnitary U V) (marginalAB X) :=
  partialTraceRight_conjugation (tensorUnitary U V) W X

theorem marginalB_conjugation (U V W : unitaryGroup Bit ℂ) (X : Matrix Triple Triple ℂ) :
    marginalB (conjugation (tensorUnitary (tensorUnitary U V) W) X) =
      conjugation V (marginalB X) := by
  rw [marginalB, marginalAB_conjugation, partialTraceLeft_conjugation]
  rfl

theorem marginalBC_conjugation (U V W : unitaryGroup Bit ℂ) (X : Matrix Triple Triple ℂ) :
    marginalBC (conjugation (tensorUnitary (tensorUnitary U V) W) X) =
      conjugation (tensorUnitary V W) (marginalBC X) := by
  unfold marginalBC
  rw [submatrix_conjugation (Equiv.prodAssoc Bit Bit Bit).symm _
    (tensorUnitary U (tensorUnitary V W)) (Matrix.kronecker_assoc' U.val V.val W.val),
    partialTraceLeft_conjugation]

theorem marginalAC_conjugation (U V W : unitaryGroup Bit ℂ) (X : Matrix Triple Triple ℂ) :
    marginalAC (conjugation (tensorUnitary (tensorUnitary U V) W) X) =
      conjugation (tensorUnitary U W) (marginalAC X) := by
  let e : Triple ≃ Triple :=
    ((Equiv.prodAssoc Bit Bit Bit).trans
      ((Equiv.refl Bit).prodCongr (Equiv.prodComm Bit Bit))).trans
        (Equiv.prodAssoc Bit Bit Bit).symm
  have he (Y : Matrix Triple Triple ℂ) :
      marginalAC Y = partialTraceRight (Y.submatrix e e) := rfl
  have hk : (tensorUnitary (tensorUnitary U V) W).val.submatrix e e =
      (tensorUnitary (tensorUnitary U W) V).val := by
    ext ⟨⟨a, c⟩, b⟩ ⟨⟨a', c'⟩, b'⟩
    change (U.val a a' * V.val b b') * W.val c c' =
      (U.val a a' * W.val c c') * V.val b b'
    rw [mul_right_comm]
  rw [he, submatrix_conjugation e _ _ hk, partialTraceRight_conjugation, ← he]

/-- Both terms in equation (357) use the corresponding product basis, with
the same rotation on the reference and the C subsystem. -/
theorem reverseCMI_conjugation (t : ℝ) (U V W : unitaryGroup Bit ℂ)
    (τ : DensityState Bit) (X : Matrix Triple Triple ℂ) :
    reverseCMI t (conjugateDensity W τ)
      (conjugation (tensorUnitary (tensorUnitary U V) W) X) =
      reverseCMI t τ X := by
  simp only [reverseCMI, toMatrix_conjugateDensity, marginalAB_conjugation,
    marginalB_conjugation, marginalBC_conjugation, ← conjugation_tensor,
    geodesicRelativeEntropy_conjugation]

end ProductCovariance

/-- The faithful standard-coordinate fiber for the transported counterexample. -/
def NativeFixedMarginals (U : unitaryGroup Bit ℂ) (ρ : DensityState Triple) : Prop :=
  (toMatrix ρ).PosDef ∧
    marginalAB (toMatrix ρ) = diagReal pairLaw ∧
    marginalAC (toMatrix ρ) = conjugation (tensorUnitary 1 U) (diagReal pairLaw) ∧
    marginalBC (toMatrix ρ) = conjugation (tensorUnitary 1 U) (diagReal pairLaw)

private theorem conjugateDensity_mem_nativeFiber (U : unitaryGroup Bit ℂ)
    (ρ : DensityState Triple) (hρ : FixedMarginals ρ) :
    NativeFixedMarginals U (conjugateDensity (tensorUnitary (tensorUnitary 1 1) U) ρ) := by
  rcases hρ with ⟨hpos, _, hAB, hAC, hBC⟩
  rw [NativeFixedMarginals, toMatrix_conjugateDensity]
  let K : unitaryGroup Triple ℂ := tensorUnitary (tensorUnitary 1 1) U
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [conjugation_apply]
    have hK : K.val * K.valᴴ = 1 := Unitary.coe_mul_star_self K
    have hinj : Function.Injective K.valᴴ.mulVec := by
      intro x y h
      have he := congrArg (fun v => K.val *ᵥ v) h
      simpa only [Matrix.mulVec_mulVec, hK, Matrix.one_mulVec] using he
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hpos.conjTranspose_mul_mul_same hinj
  · rw [marginalAB_conjugation, hAB]
    have hI : tensorUnitary (1 : unitaryGroup Bit ℂ) (1 : unitaryGroup Bit ℂ) = 1 := by
      apply Subtype.ext
      exact Matrix.one_kronecker_one
    rw [hI]
    simp
  · rw [marginalAC_conjugation, hAC]
  · rw [marginalBC_conjugation, hBC]

/-- For every fixed faithful qubit reference, a single faithful pair-marginal
fiber in standard coordinates already rules out a trace-distance modulus. -/
theorem native_result (t : ℝ) (τ : DensityState Bit) (hτ : (toMatrix τ).PosDef) :
    ¬ ∃ ω : ℝ → ℝ, Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
      ∀ ρ σ : DensityState Triple,
        NativeFixedMarginals hτ.isHermitian.eigenvectorUnitary ρ →
        NativeFixedMarginals hτ.isHermitian.eigenvectorUnitary σ →
        |reverseCMI t τ (toMatrix ρ) - reverseCMI t τ (toMatrix σ)| ≤
          ω (traceDistance ρ σ) := by
  rintro ⟨ω, hω, hbound⟩
  obtain ⟨a, ha, hsum, hdiag⟩ := referenceInEigenbasis τ hτ
  let U := hτ.isHermitian.eigenvectorUnitary
  let K : unitaryGroup Triple ℂ := tensorUnitary (tensorUnitary 1 1) U
  let τdiag := diagonalState a ha hsum
  have hτeq : conjugateDensity U τdiag = τ := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change toMatrix (conjugateDensity U τdiag) = toMatrix τ
    rw [toMatrix_conjugateDensity]
    exact hdiag.symm
  apply result
  refine ⟨t, a, ha, hsum, ω, hω, ?_⟩
  intro ρ σ hρ hσ
  have h := hbound (conjugateDensity K ρ) (conjugateDensity K σ)
    (conjugateDensity_mem_nativeFiber U ρ hρ) (conjugateDensity_mem_nativeFiber U σ hσ)
  rw [← hτeq] at h
  simpa only [toMatrix_conjugateDensity, traceDistance_conjugateDensity, K,
    reverseCMI_conjugation] using h

/-- Negative answer to the reverse part of Open Question 6 at three qubits.
The modulus may depend on both the interpolation parameter and the faithful
reference. -/
theorem noDimensionOnlyModulus (t : ℝ) (τ : DensityState Bit)
    (hτ : (toMatrix τ).PosDef) :
    ¬ ∃ ω : ℝ → ℝ, Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
      ∀ ρ σ : DensityState Triple, (toMatrix ρ).PosDef → (toMatrix σ).PosDef →
        |reverseCMI t τ (toMatrix ρ) - reverseCMI t τ (toMatrix σ)| ≤
          ω (traceDistance ρ σ) := by
  rintro ⟨ω, hω, hbound⟩
  exact native_result t τ hτ
    ⟨ω, hω, fun ρ σ hρ hσ => hbound ρ σ hρ.1 hσ.1⟩

end
end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
