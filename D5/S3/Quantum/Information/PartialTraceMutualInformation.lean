/- GID: D5/S3/Quantum/Information/PartialTraceMutualInformation
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/PartialTraceMutualInformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Partial traces preserve density states and determine quantum mutual information. -/

import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/- The trace-preservation and positivity proofs below are adapted from
   CsdLean4/Mathlib/LinearAlgebra/Matrix/PartialTrace.lean,
   zblore/csd-lean4 revision 13eda16971c66de4bc9f550e418dd4fdf59a5121.
   Copyright (c) 2026 Zayn Blore. All rights reserved.
   Released under Apache 2.0; full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
   Entropy and TraceDistance from the same upstream supply the spectral proofs below.
   Changes: specialize to complex matrices, retain partialTrace, and adapt to CStarMatrix.
   Retire these ports when this repository's pinned Mathlib supplies equivalent declarations.
   Search receipts and the revised registration are in docs/reports/qmutualinfo/.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.PartialTraceMutualInformation

open scoped BigOperators ComplexOrder Kronecker Matrix
open scoped MatrixOrder
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching

noncomputable def partialTraceLeft {A B : Type*} [Fintype A]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun b d => ∑ a, joint (a, b) (a, d)

noncomputable def partialTraceRight {A B : Type*} [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a c => ∑ b, joint (a, b) (c, b)

theorem partialTraceLeft_add {A B : Type*} [Fintype A]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft (x + y) = partialTraceLeft x + partialTraceLeft y := by
  ext b d
  simp [partialTraceLeft, Finset.sum_add_distrib]

theorem partialTraceRight_add {A B : Type*} [Fintype B]
    (x y : Matrix (A × B) (A × B) ℂ) :
    partialTraceRight (x + y) = partialTraceRight x + partialTraceRight y := by
  ext a c
  simp [partialTraceRight, Finset.sum_add_distrib]

theorem partialTraceLeft_kronecker {A B : Type*} [Fintype A]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceLeft (Matrix.kronecker x y) = Matrix.trace x • y := by
  ext b d
  simp [partialTraceLeft, Matrix.trace, Finset.mul_sum, mul_comm]

theorem partialTraceRight_kronecker {A B : Type*} [Fintype B]
    (x : Matrix A A ℂ) (y : Matrix B B ℂ) :
    partialTraceRight (Matrix.kronecker x y) = Matrix.trace y • x := by
  ext a c
  simp [partialTraceRight, Matrix.trace, Finset.mul_sum, mul_comm]

theorem trace_partialTraceLeft {A B : Type*} [Fintype A] [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceLeft joint) = Matrix.trace joint := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceLeft]
  exact (Fintype.sum_prod_type_right fun p : A × B => joint p p).symm

theorem trace_partialTraceRight {A B : Type*} [Fintype A] [Fintype B]
    (joint : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTraceRight joint) = Matrix.trace joint := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceRight]
  exact (Fintype.sum_prod_type fun p : A × B => joint p p).symm

theorem partialTraceLeft_posSemidef {A B : Type*} [Fintype A]
    {joint : Matrix (A × B) (A × B) ℂ} (h : joint.PosSemidef) :
    (partialTraceLeft joint).PosSemidef := by
  have heq : partialTraceLeft joint =
      ∑ a : A, joint.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b d
    simp [partialTraceLeft, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun a _ => h.submatrix (fun b => (a, b)))

theorem partialTraceRight_posSemidef {A B : Type*} [Fintype B]
    {joint : Matrix (A × B) (A × B) ℂ} (h : joint.PosSemidef) :
    (partialTraceRight joint).PosSemidef := by
  have heq : partialTraceRight joint =
      ∑ b : B, joint.submatrix (fun a => (a, b)) (fun a => (a, b)) := by
    ext a c
    simp [partialTraceRight, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun b _ => h.submatrix (fun a => (a, b)))

/-- Trace out the left factor, retaining the state on `B`. -/
noncomputable def marginalLeft
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : DensityState (A × B)) : DensityState B := by
  refine ⟨CStarMatrix.ofMatrix (partialTraceLeft rho.1), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    apply partialTraceLeft_posSemidef
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
  · exact (trace_partialTraceLeft rho.1).trans rho.2.2

/-- Trace out the right factor, retaining the state on `A`. -/
noncomputable def marginalRight
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : DensityState (A × B)) : DensityState A := by
  refine ⟨CStarMatrix.ofMatrix (partialTraceRight rho.1), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    apply Matrix.PosSemidef.nonneg
    apply partialTraceRight_posSemidef
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)
  · exact (trace_partialTraceRight rho.1).trans rho.2.2

/-- Mutual information of a joint state, with both marginals obtained by partial trace. -/
noncomputable def quantumMutualInformation
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : DensityState (A × B)) : ℝ :=
  vonNeumannEntropy (marginalRight rho) + vonNeumannEntropy (marginalLeft rho) -
    vonNeumannEntropy rho

private theorem density_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) : (CStarMatrix.ofMatrix.symm rho.1).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)

/-- Independent density states form a density state by the Kronecker product. -/
noncomputable def productState
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : DensityState A) (sigma : DensityState B) : DensityState (A × B) := by
  refine ⟨CStarMatrix.ofMatrix (rho.1 ⊗ₖ sigma.1), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef rho).kronecker (density_posSemidef sigma)).nonneg
  · exact (Matrix.trace_kronecker rho.1 sigma.1).trans (by rw [rho.2.2, sigma.2.2, mul_one])

theorem marginalLeft_productState
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : DensityState A) (sigma : DensityState B) :
    marginalLeft (productState rho sigma) = sigma := by
  have htr : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 := rho.2.2
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix
    ((partialTraceLeft_kronecker (CStarMatrix.ofMatrix.symm rho.1)
      (CStarMatrix.ofMatrix.symm sigma.1)).trans (by rw [htr, one_smul]; rfl))

theorem marginalRight_productState
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : DensityState A) (sigma : DensityState B) :
    marginalRight (productState rho sigma) = rho := by
  have htr : Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 := sigma.2.2
  apply Subtype.ext
  exact congrArg CStarMatrix.ofMatrix
    ((partialTraceRight_kronecker (CStarMatrix.ofMatrix.symm rho.1)
      (CStarMatrix.ofMatrix.symm sigma.1)).trans (by rw [htr, one_smul]; rfl))

section SpectralPorts

open Matrix Polynomial
variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def spectralEntropy {rho : Matrix n n ℂ} (h : rho.IsHermitian) : ℝ :=
  ∑ i, Real.negMulLog (h.eigenvalues i)

private theorem charpoly_conj_unitary {ρ U : Matrix n n ℂ} (hU : star U * U = 1) :
    (U * ρ * star U).charpoly = ρ.charpoly := by
  rw [Matrix.charpoly_mul_comm (U * ρ) (star U), ← Matrix.mul_assoc, hU, Matrix.one_mul]

omit [Fintype n] [DecidableEq n] in
private theorem isHermitian_kronecker {m : Type*} {ρ : Matrix n n ℂ}
    {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ ⊗ₖ σ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_kronecker, hρ.eq, hσ.eq]

private theorem spectral_sum_eq_of_charpoly_prod
    {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℂ} (hA : A.IsHermitian)
    (d : k → ℝ) (g : ℝ → ℝ)
    (h : A.charpoly = ∏ c, (X - C ((RCLike.ofReal (d c)) : ℂ))) :
    ∑ c, g (hA.eigenvalues c) = ∑ c, g (d c) := by
  have hroots1 : A.charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val :=
    hA.roots_charpoly_eq_eigenvalues
  have hroots2 : A.charpoly.roots
      = Multiset.map (fun c => (RCLike.ofReal (d c) : ℂ)) Finset.univ.val := by
    rw [h, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  have hmap : Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val
      = Multiset.map (fun c => (RCLike.ofReal (d c) : ℂ)) Finset.univ.val := by
    rw [← hroots1, hroots2]
  have hcongr := congrArg (fun s => (Multiset.map (fun z : ℂ => g (RCLike.re z)) s).sum) hmap
  simp only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_re] at hcongr
  rw [Finset.sum, Finset.sum]
  exact hcongr

private theorem kronecker_eq_conj_diagonal_eigenvalues {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (ρ ⊗ₖ σ)
      = ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
        * diagonal (fun p : n × m =>
            (RCLike.ofReal (hρ.eigenvalues p.1) : ℂ) * RCLike.ofReal (hσ.eigenvalues p.2))
        * star ((hρ.eigenvectorUnitary : Matrix n n ℂ)
            ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ)) := by
  conv_lhs => rw [hρ.spectral_theorem, hσ.spectral_theorem,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker]
  rw [← diagonal_kronecker_diagonal (fun i => (RCLike.ofReal (hρ.eigenvalues i) : ℂ))
        (fun j => (RCLike.ofReal (hσ.eigenvalues j) : ℂ)),
    mul_kronecker_mul, mul_kronecker_mul]
  rfl

private theorem star_kronecker_eigenvectorUnitary_mul_self {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
      * ((hρ.eigenvectorUnitary : Matrix n n ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix m m ℂ))
      = 1 := by
  rw [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, ← Matrix.star_eq_conjTranspose,
    ← Matrix.star_eq_conjTranspose, ← mul_kronecker_mul,
    Unitary.coe_star_mul_self, Unitary.coe_star_mul_self, one_kronecker_one]

private theorem spectral_sum_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (g : ℝ → ℝ) :
    ∑ c, g ((isHermitian_kronecker hρ hσ).eigenvalues c)
      = ∑ i, ∑ j, g (hρ.eigenvalues i * hσ.eigenvalues j) := by
  have hchar : (ρ ⊗ₖ σ).charpoly
      = ∏ p : n × m, (X - C ((RCLike.ofReal (hρ.eigenvalues p.1 * hσ.eigenvalues p.2)) : ℂ)) := by
    rw [kronecker_eq_conj_diagonal_eigenvalues hρ hσ,
      charpoly_conj_unitary (star_kronecker_eigenvectorUnitary_mul_self hρ hσ),
      charpoly_diagonal]
    exact Finset.prod_congr rfl fun p _ => by rw [RCLike.ofReal_mul]
  rw [spectral_sum_eq_of_charpoly_prod (isHermitian_kronecker hρ hσ)
    (fun p => hρ.eigenvalues p.1 * hσ.eigenvalues p.2) g hchar,
    ← Finset.univ_product_univ, Finset.sum_product]

private theorem spectralEntropy_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {σ : Matrix m m ℂ}
    (hpsdρ : ρ.PosSemidef) (hpsdσ : σ.PosSemidef)
    (htrρ : ρ.trace = 1) (htrσ : σ.trace = 1) :
    spectralEntropy (isHermitian_kronecker hpsdρ.1 hpsdσ.1)
      = spectralEntropy hpsdρ.1 + spectralEntropy hpsdσ.1 := by
  have hsumρ : ∑ i, hpsdρ.1.eigenvalues i = 1 := by
    have h := hpsdρ.1.trace_eq_sum_eigenvalues
    rw [htrρ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  have hsumσ : ∑ j, hpsdσ.1.eigenvalues j = 1 := by
    have h := hpsdσ.1.trace_eq_sum_eigenvalues
    rw [htrσ] at h
    have hre := congrArg Complex.re h
    rw [Complex.one_re, Complex.re_sum] at hre
    simpa using hre.symm
  rw [spectralEntropy, spectralEntropy, spectralEntropy,
    spectral_sum_kronecker hpsdρ.1 hpsdσ.1 Real.negMulLog]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Real.negMulLog_mul _ _))]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [show (∑ i : n, ∑ j : m, hpsdσ.1.eigenvalues j * Real.negMulLog (hpsdρ.1.eigenvalues i))
        = ∑ i : n, (∑ j : m, hpsdσ.1.eigenvalues j) * Real.negMulLog (hpsdρ.1.eigenvalues i) from
          Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul]]
    simp_rw [hsumσ, one_mul]
  · rw [show (∑ i : n, ∑ j : m, hpsdρ.1.eigenvalues i * Real.negMulLog (hpsdσ.1.eigenvalues j))
        = ∑ i : n, hpsdρ.1.eigenvalues i * ∑ j : m, Real.negMulLog (hpsdσ.1.eigenvalues j) from
          Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum]]
    rw [← Finset.sum_mul, hsumρ, one_mul]

private theorem re_trace_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq f]
  unfold Matrix.IsHermitian.cfc
  have huu : star (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, huu, one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

private theorem entropy_eq_spectral (rho : DensityState n) :
    vonNeumannEntropy rho = spectralEntropy (density_posSemidef rho).isHermitian := by
  let M : Matrix n n ℂ := CStarMatrix.ofMatrix.symm rho.1
  have hM : M.IsHermitian := (density_posSemidef rho).isHermitian
  have hlog : CStarMatrix.ofMatrix (cfc Real.log M) = CFC.log rho.1 := by
    exact StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _)
      CStarMatrix.ofMatrixL.continuous hM (by exact hM)
  have hmul : M * cfc Real.log M = cfc (fun x : ℝ => x * Real.log x) M := by
    conv_lhs => lhs; rw [← cfc_id ℝ M hM]
    exact (cfc_mul id Real.log M (M.finite_real_spectrum.continuousOn _)
      (M.finite_real_spectrum.continuousOn _)).symm
  unfold vonNeumannEntropy
  rw [← hlog]
  change -(Matrix.trace (M * cfc Real.log M)).re = _
  rw [hmul, re_trace_cfc hM, spectralEntropy, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [Real.negMulLog]

end SpectralPorts

/-- Entropy is additive for every pair of density states, including singular states. -/
theorem vonNeumannEntropy_productState
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : DensityState A) (sigma : DensityState B) :
    vonNeumannEntropy (productState rho sigma) =
      vonNeumannEntropy rho + vonNeumannEntropy sigma := by
  rw [entropy_eq_spectral, entropy_eq_spectral, entropy_eq_spectral]
  exact spectralEntropy_kronecker (density_posSemidef rho) (density_posSemidef sigma)
    rho.2.2 sigma.2.2

/-- Independent product states have zero mutual information with their actual marginals. -/
theorem quantumMutualInformation_productState
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (rho : DensityState A) (sigma : DensityState B) :
    quantumMutualInformation (productState rho sigma) = 0 := by
  unfold quantumMutualInformation
  rw [marginalRight_productState, marginalLeft_productState, vonNeumannEntropy_productState]
  exact sub_self _

#print axioms quantumMutualInformation_productState

#print axioms partialTraceLeft_posSemidef
#print axioms partialTraceRight_posSemidef
#print axioms marginalLeft
#print axioms marginalRight

end D5.S3.Quantum.Information.PartialTraceMutualInformation
