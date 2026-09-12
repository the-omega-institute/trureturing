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
   The trace-to-spectrum calculation follows the imported module's spectral port from
   zblore/csd-lean4 revision 13eda16971c66de4bc9f550e418dd4fdf59a5121.
   Copyright (c) 2026 Zayn Blore. All rights reserved. Apache 2.0 license;
   full license: docs/reports/qmutualinfo/csd-lean4-LICENSE.txt.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.InputInformationBalance

open scoped BigOperators ComplexOrder MatrixOrder Matrix
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
  have hz (k : ℕ) : (k • ({0} : Multiset ℂ)).filter (· ≠ 0) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    simp
  simpa [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero, hz] using h

private theorem sum_filter_zero (s : Multiset ℂ) (f : ℂ → ℝ) (hf : f 0 = 0) :
    ((s.filter (· ≠ 0)).map f).sum = (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    by_cases hz : z = 0
    · subst z; simp [hf, ih]
    · simp [hz, ih]

private theorem entropy_eq_of_nonzero_roots (rho : DensityState A) (sigma : DensityState B)
    (h : (CStarMatrix.ofMatrix.symm rho.1).charpoly.roots.filter (· ≠ 0) =
      (CStarMatrix.ofMatrix.symm sigma.1).charpoly.roots.filter (· ≠ 0)) :
    vonNeumannEntropy rho = vonNeumannEntropy sigma := by
  have hs := congrArg
    (fun s : Multiset ℂ => (s.map (fun z => Real.negMulLog z.re)).sum) h
  rw [sum_filter_zero _ _ (by simp), sum_filter_zero _ _ (by simp),
    (density_hermitian rho).roots_charpoly_eq_eigenvalues,
    (density_hermitian sigma).roots_charpoly_eq_eigenvalues] at hs
  simp only [Multiset.map_map, Function.comp_def] at hs
  rw [entropy_eq_sum, entropy_eq_sum]
  exact hs

/-- Both complementary marginals of any finite pure density state have the same entropy. -/
theorem pure_complementary_entropy (rho : DensityState (A × B)) (hp : IsPure rho) :
    vonNeumannEntropy (marginalLeft rho) = vonNeumannEntropy (marginalRight rho) := by
  obtain ⟨v, hv⟩ := hp
  let M : Matrix A B ℂ := fun a b => v (a, b)
  have hl : CStarMatrix.ofMatrix.symm (marginalLeft rho).1 = (Mᴴ * M)ᵀ := by
    ext b d
    change (∑ a, rho.1 (a, b) (a, d)) = ∑ a, star (v (a, d)) * v (a, b)
    exact Finset.sum_congr rfl fun a _ => (hv _ _).trans (mul_comm _ _)
  have hr : CStarMatrix.ofMatrix.symm (marginalRight rho).1 = M * Mᴴ := by
    ext a c
    change (∑ b, rho.1 (a, b) (c, b)) = ∑ b, v (a, b) * star (v (c, b))
    exact Finset.sum_congr rfl fun b _ => hv _ _
  apply entropy_eq_of_nonzero_roots
  rw [hl, hr, Matrix.charpoly_transpose]
  exact nonzero_roots_mul_comm Mᴴ M

/-- Relabel a density state along an equivalence, retaining every matrix entry. -/
def relabel {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : m ≃ n) (rho : DensityState n) : DensityState m := by
  refine ⟨CStarMatrix.ofMatrix (rho.1.submatrix e e), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact ((Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1)).submatrix e).nonneg
  · exact (e.sum_comp (fun i => rho.1 i i)).trans rho.2.2

private theorem isPure_relabel {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (e : m ≃ n) (rho : DensityState n) (hp : IsPure rho) :
    IsPure (relabel e rho) := by
  obtain ⟨v, hv⟩ := hp
  exact ⟨v ∘ e, fun i j => hv (e i) (e j)⟩

private def arGrouping : (A × R) × B ≃ A × B × R :=
  (Equiv.prodAssoc A R B).trans
    (Equiv.prodCongr (Equiv.refl A) (Equiv.prodComm R B))

/-- The AB state is obtained from the single global state by tracing out R. -/
def stateAB (rho : DensityState (A × B × R)) : DensityState (A × B) :=
  marginalRight (relabel (Equiv.prodAssoc A B R) rho)

/-- The AR state is obtained from that same global state by tracing out B. -/
def stateAR (rho : DensityState (A × B × R)) : DensityState (A × R) :=
  marginalRight (relabel arGrouping rho)

private theorem ab_retains_A (rho : DensityState (A × B × R)) :
    marginalRight (stateAB rho) = marginalRight rho := by
  apply Subtype.ext
  ext a c
  change (∑ b, ∑ r, rho.1 (a, b, r) (c, b, r)) = ∑ p : B × R, rho.1 (a, p) (c, p)
  exact (Fintype.sum_prod_type (fun p : B × R => rho.1 (a, p) (c, p))).symm

private theorem ar_retains_A (rho : DensityState (A × B × R)) :
    marginalRight (stateAR rho) = marginalRight rho := by
  apply Subtype.ext
  ext a c
  change (∑ r, ∑ b, rho.1 (a, b, r) (c, b, r)) = ∑ p : B × R, rho.1 (a, p) (c, p)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem ar_retains_R (rho : DensityState (A × B × R)) :
    marginalLeft (stateAR rho) =
      marginalLeft (relabel (Equiv.prodAssoc A B R) rho) := by
  apply Subtype.ext
  ext r s
  change (∑ a, ∑ b, rho.1 (a, b, r) (a, b, s)) =
    ∑ p : A × B, rho.1 (p.1, p.2, r) (p.1, p.2, s)
  exact (Fintype.sum_prod_type (fun p : A × B => rho.1 (p.1, p.2, r) (p.1, p.2, s))).symm

private theorem ab_retains_B (rho : DensityState (A × B × R)) :
    marginalLeft (stateAB rho) = marginalLeft (relabel arGrouping rho) := by
  apply Subtype.ext
  ext b d
  change (∑ a, ∑ r, rho.1 (a, b, r) (a, d, r)) =
    ∑ p : A × R, rho.1 (p.1, b, p.2) (p.1, d, p.2)
  exact (Fintype.sum_prod_type (fun p : A × R => rho.1 (p.1, b, p.2) (p.1, d, p.2))).symm

/-- In a pure ABR state, its actual AR and AB mutual informations sum to twice S(A). -/
theorem input_information_balance (rho : DensityState (A × B × R)) (hp : IsPure rho) :
    quantumMutualInformation (stateAR rho) + quantumMutualInformation (stateAB rho) =
      2 * vonNeumannEntropy (marginalRight rho) := by
  have hAB := pure_complementary_entropy (relabel (Equiv.prodAssoc A B R) rho)
    (isPure_relabel _ rho hp)
  have hAR := pure_complementary_entropy (relabel (arGrouping (A := A) (B := B) (R := R)) rho)
    (isPure_relabel _ rho hp)
  change vonNeumannEntropy (marginalLeft (relabel (Equiv.prodAssoc A B R) rho)) =
    vonNeumannEntropy (stateAB rho) at hAB
  change vonNeumannEntropy (marginalLeft (relabel arGrouping rho)) =
    vonNeumannEntropy (stateAR rho) at hAR
  unfold quantumMutualInformation
  rw [ar_retains_A, ab_retains_A, ar_retains_R, ab_retains_B, hAB, hAR]
  ring

#print axioms pure_complementary_entropy
#print axioms input_information_balance

end
end D5.S3.Quantum.Information.InputInformationBalance
