/- GID: D5/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/ToeplitzFlatFloorMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A contact Gram update has floor omega with multiplicity at least N plus one minus M. -/

import Mathlib

/- Library-search audit trail (2026-08-29):
   * Exact D5 searches for Toeplitz flat floors, contact-vector Gram updates,
     and minimum-eigenvalue multiplicity found no existing theorem.
   * Body-shape searches for the weighted unit-circle Vandermonde analysis
     matrix found no canonical D5 primitive to reuse; no definition or
     abbreviation is introduced here.
   * Pinned Mathlib's `posSemidef_conjTranspose_mul_self` supplies positivity,
     `LinearMap.finrank_range_add_finrank_ker` supplies the nullity bound, and
     `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` supplies the real
     spectral carrier. All three exact hits are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Matrix
open scoped ComplexConjugate ComplexOrder

namespace D5.S3.Observer.Tomography.ToeplitzFlatFloorMultiplicity

/-- Let `M` strictly positive contact atoms lie on the complex unit circle.
Their weighted contact-vector analysis matrix constructs the Toeplitz
covariance as a white scalar floor plus an adjoint Gram update. If `M < N+1`,
then the least real spectral value is exactly the floor `omega`, and its
Hermitian eigenspace has dimension at least `N+1-M`. For a Hermitian matrix
this eigenspace dimension is the eigenvalue multiplicity. -/
theorem toeplitz_flat_floor_multiplicity
    (N M : Nat)
    (omega : Real)
    (contact : Fin M -> unitary Complex)
    (weight : Fin M -> {q : Real // 0 < q})
    (contacts_lt : M < N + 1) :
    let analysis : Matrix (Fin M) (Fin (N + 1)) Complex := fun r j =>
      (Real.sqrt (weight r).1 : Complex) *
        star ((contact r : Complex) ^ j.val)
    let toeplitz :=
      (omega : Complex) •
          (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
        analysis.conjTranspose * analysis
    (forall j k, toeplitz j k =
      (if j = k then (omega : Complex) else 0) +
        ∑ r, ((weight r).1 : Complex) *
          (contact r : Complex) ^ j.val *
            star ((contact r : Complex) ^ k.val)) /\
      IsLeast (spectrum Real toeplitz) omega /\
      N + 1 - M <= Module.finrank Complex
        (Module.End.eigenspace toeplitz.mulVecLin (omega : Complex)) := by
  dsimp only
  let analysis : Matrix (Fin M) (Fin (N + 1)) Complex := fun r j =>
    (Real.sqrt (weight r).1 : Complex) *
      star ((contact r : Complex) ^ j.val)
  let toeplitz :=
    (omega : Complex) •
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
      analysis.conjTranspose * analysis
  change (forall j k, toeplitz j k =
      (if j = k then (omega : Complex) else 0) +
        ∑ r, ((weight r).1 : Complex) *
          (contact r : Complex) ^ j.val *
            star ((contact r : Complex) ^ k.val)) /\
    IsLeast (spectrum Real toeplitz) omega /\
    N + 1 - M <= Module.finrank Complex
      (Module.End.eigenspace toeplitz.mulVecLin (omega : Complex))
  have residualPositive :
      (analysis.conjTranspose * analysis).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self analysis
  have toeplitzHermitian : toeplitz.IsHermitian := by
    exact (Matrix.isHermitian_one.smul (by
      change star (omega : Complex) = (omega : Complex)
      exact Complex.conj_ofReal omega)).add residualPositive.isHermitian
  have rangeBound :
      Module.finrank Complex analysis.mulVecLin.range <= M := by
    calc
      Module.finrank Complex analysis.mulVecLin.range <=
          Module.finrank Complex (Fin M -> Complex) := Submodule.finrank_le _
      _ = M := by simp
  have rankNullity := analysis.mulVecLin.finrank_range_add_finrank_ker
  have domainRank :
      Module.finrank Complex (Fin (N + 1) -> Complex) = N + 1 := by
    simp
  have kernelBound :
      N + 1 - M <= Module.finrank Complex analysis.mulVecLin.ker := by
    omega
  have kernelLeEigenspace :
      analysis.mulVecLin.ker <=
        Module.End.eigenspace toeplitz.mulVecLin (omega : Complex) := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff]
    change toeplitz *ᵥ x = (omega : Complex) • x
    change analysis *ᵥ x = 0 at hx
    have residualZero :
        (analysis.conjTranspose * analysis) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec x analysis.conjTranspose analysis,
        hx, Matrix.mulVec_zero]
    simp [toeplitz, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, residualZero]
  have multiplicityBound :
      N + 1 - M <= Module.finrank Complex
        (Module.End.eigenspace toeplitz.mulVecLin (omega : Complex)) :=
    kernelBound.trans (Submodule.finrank_mono kernelLeEigenspace)
  have kernelPositive :
      0 < Module.finrank Complex analysis.mulVecLin.ker := by
    omega
  obtain ⟨x, x_ne_zero⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp kernelPositive
  have omegaEigenvector :
      Module.End.HasEigenvector toeplitz.mulVecLin
        (omega : Complex) x.1 :=
    ⟨kernelLeEigenspace x.2, by simpa using x_ne_zero⟩
  have omegaComplexSpectrum :
      (omega : Complex) ∈ spectrum Complex toeplitz := by
    rw [← Matrix.spectrum_toLin' toeplitz, Matrix.toLin'_apply']
    exact
      (Module.End.hasEigenvalue_of_hasEigenvector omegaEigenvector).mem_spectrum
  have omegaRealSpectrum : omega ∈ spectrum Real toeplitz :=
    (spectrum.algebraMap_mem_iff Complex).mp omegaComplexSpectrum
  refine ⟨?_, ⟨omegaRealSpectrum, ?_⟩, multiplicityBound⟩
  · intro j k
    change (((omega : Complex) •
        (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
      analysis.conjTranspose * analysis) j k) = _
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]
    simp only [Matrix.one_apply, smul_eq_mul]
    have floorEntry :
        (omega : Complex) * (if j = k then 1 else 0) =
          if j = k then (omega : Complex) else 0 := by
      split <;> simp_all
    rw [floorEntry]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    change star ((Real.sqrt (weight r).1 : Complex) *
        star ((contact r : Complex) ^ j.val)) *
        ((Real.sqrt (weight r).1 : Complex) *
          star ((contact r : Complex) ^ k.val)) = _
    rw [star_mul, star_star]
    have sqrtSquare :
        Real.sqrt (weight r).1 * Real.sqrt (weight r).1 =
          (weight r).1 := by
      nlinarith [Real.sq_sqrt (weight r).2.le]
    have starSqrt :
        star (Real.sqrt (weight r).1 : Complex) =
          (Real.sqrt (weight r).1 : Complex) :=
      Complex.conj_ofReal _
    have sqrtSquareComplex :
        (Real.sqrt (weight r).1 : Complex) *
            (Real.sqrt (weight r).1 : Complex) =
          ((weight r).1 : Complex) := by
      exact_mod_cast sqrtSquare
    rw [starSqrt]
    calc
      _ = ((Real.sqrt (weight r).1 : Complex) *
            (Real.sqrt (weight r).1 : Complex)) *
          (contact r : Complex) ^ j.val *
            star ((contact r : Complex) ^ k.val) := by ring
      _ = _ := by rw [sqrtSquareComplex]
  · intro lambda lambdaSpectrum
    rw [toeplitzHermitian.spectrum_real_eq_range_eigenvalues] at lambdaSpectrum
    obtain ⟨i, rfl⟩ := lambdaSpectrum
    let v : Fin (N + 1) -> Complex :=
      toeplitzHermitian.eigenvectorBasis i
    have residualNonnegative := residualPositive.re_dotProduct_nonneg v
    have vUnit : star v ⬝ᵥ v = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
      rw [inner_self_eq_norm_sq_to_K,
        toeplitzHermitian.eigenvectorBasis.norm_eq_one]
      norm_num
    have eigenvalueDecomposition :
        toeplitzHermitian.eigenvalues i =
          omega + RCLike.re
            (star v ⬝ᵥ (analysis.conjTranspose * analysis) *ᵥ v) := by
      rw [toeplitzHermitian.eigenvalues_eq]
      change Complex.re (star v ⬝ᵥ toeplitz *ᵥ v) =
        omega + Complex.re
          (star v ⬝ᵥ (analysis.conjTranspose * analysis) *ᵥ v)
      change Complex.re
          (star v ⬝ᵥ
            (((omega : Complex) •
                (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) Complex) +
              analysis.conjTranspose * analysis) *ᵥ v)) = _
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      congr 1
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, vUnit]
      simp
    rw [eigenvalueDecomposition]
    exact le_add_of_nonneg_right residualNonnegative

#print axioms toeplitz_flat_floor_multiplicity

end D5.S3.Observer.Tomography.ToeplitzFlatFloorMultiplicity
