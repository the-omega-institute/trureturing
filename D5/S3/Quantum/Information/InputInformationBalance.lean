/- GID: D5/S3/Quantum/Information/InputInformationBalance
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/InputInformationBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A pure state's complementary entropies give the input information balance. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation

/- The nonzero-root proof is adapted from physlib, QuantumInfo/Entropy/VonNeumann.lean,
   revision 889c09c66fb5f3c4a27182a43cafbed9e00b9d0a, Sᵥₙ_of_partial_eq and its helpers.
   Copyright (c) 2025 Alex Meiburg. All rights reserved. Apache 2.0 license;
   full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
   Changes: use DensityState, the existing partial traces, and CStarMatrix trace entropy.
   Retire this port when the repository's pinned Mathlib provides equivalent declarations.
   The trace-to-spectrum calculation follows the imported module's spectral port.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.InputInformationBalance

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

variable {A B R : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype R] [DecidableEq R]

/-- A density state is pure when it is the outer product of one amplitude vector. -/
def IsPure {n : Type*} [Fintype n] [DecidableEq n] (rho : DensityState n) : Prop :=
  ∃ v : n → ℂ, ∀ i j, rho.1 i j = v i * star (v j)

private theorem density_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)).isHermitian

private theorem entropy_eq_sum {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) :
    vonNeumannEntropy rho = ∑ i, Real.negMulLog ((density_hermitian rho).eigenvalues i) := by
  let M : Matrix n n ℂ := CStarMatrix.ofMatrix.symm rho.1
  have hM : M.IsHermitian := density_hermitian rho
  have hlog : CStarMatrix.ofMatrix (cfc Real.log M) = CFC.log rho.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log M
      (M.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hM hM
  have hmul : M * cfc Real.log M = cfc (fun x : ℝ => x * Real.log x) M := by
    conv_lhs => lhs; rw [← cfc_id ℝ M hM]
    exact (cfc_mul id Real.log M (M.finite_real_spectrum.continuousOn _)
      (M.finite_real_spectrum.continuousOn _)).symm
  unfold vonNeumannEntropy
  rw [← hlog]
  change -(Matrix.trace (M * cfc Real.log M)).re = _
  rw [hmul, hM.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal, Complex.re_sum,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [Real.negMulLog]

private theorem nonzero_roots_mul_comm (M : Matrix A B ℂ) (N : Matrix B A ℂ) :
    (M * N).charpoly.roots.filter (· ≠ 0) =
      (N * M).charpoly.roots.filter (· ≠ 0) := by
  have h := congrArg (fun p : Polynomial ℂ => p.roots.filter (· ≠ 0))
    (Matrix.charpoly_mul_comm' M N)
  simpa [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero] using h

private theorem entropy_eq_of_nonzero_roots (rho : DensityState A) (sigma : DensityState B)
    (h : (CStarMatrix.ofMatrix.symm rho.1).charpoly.roots.filter (· ≠ 0) =
      (CStarMatrix.ofMatrix.symm sigma.1).charpoly.roots.filter (· ≠ 0)) :
    vonNeumannEntropy rho = vonNeumannEntropy sigma := by
  rw [(density_hermitian rho).roots_charpoly_eq_eigenvalues,
    (density_hermitian sigma).roots_charpoly_eq_eigenvalues] at h
  have hs := congrArg
    (fun s : Multiset ℂ => (s.map (fun z => Real.negMulLog z.re)).sum) h
  simp only [Multiset.filter_map, Multiset.map_map, Function.comp_apply,
    RCLike.ofReal_re] at hs
  rw [entropy_eq_sum, entropy_eq_sum]
  simpa [Finset.sum, Multiset.sum_map_filter, Real.negMulLog_zero] using hs

/-- Both complementary marginals of any finite pure density state have the same entropy. -/
theorem pure_complementary_entropy (rho : DensityState (A × B)) (hp : IsPure rho) :
    vonNeumannEntropy (marginalLeft rho) = vonNeumannEntropy (marginalRight rho) := by
  obtain ⟨v, hv⟩ := hp
  let M : Matrix A B ℂ := fun a b => v (a, b)
  have hl : CStarMatrix.ofMatrix.symm (marginalLeft rho).1 = (Mᴴ * M)ᵀ := by
    ext b d
    simp only [marginalLeft, partialTraceLeft, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hv, M]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hr : CStarMatrix.ofMatrix.symm (marginalRight rho).1 = M * Mᴴ := by
    ext a c
    simp [marginalRight, partialTraceRight, Matrix.mul_apply, hv, M]
  apply entropy_eq_of_nonzero_roots
  rw [hl, hr, Matrix.charpoly_transpose]
  exact nonzero_roots_mul_comm Mᴴ M

end
end D5.S3.Quantum.Information.InputInformationBalance
