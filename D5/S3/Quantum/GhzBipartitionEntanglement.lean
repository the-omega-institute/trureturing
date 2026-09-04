/- GID: D5/S3/Quantum/GhzBipartitionEntanglement
   generality: G
   mirror-B: D5/B/S3/Quantum/GhzBipartitionEntanglement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nonempty bipartition of a finite GHZ state has rank two and entropy log two. -/

import Mathlib.Algebra.Star.CHSH
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * `BellPureStateMixedMarginal` proves the two-qubit marginal, and
     `BellPairLocalGlobalResidual` distinguishes two Bell phases, but neither treats arbitrary
     nonempty bipartitions or identifies their Schmidt rank and entropy.
   * Repository searches for GHZ, Schmidt, multipartite entropy, and rank-two reduced spectra
     found no exact theorem or more general owner.
   * Pinned Mathlib supplies `Matrix.rank_of_det_ne_zero`, `Matrix.det_fin_two`,
     `TsirelsonInequality.sqrt_two_inv_mul_self`, and `Real.log_inv`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.GhzBipartitionEntanglement

/-- The all-zero or all-one local configuration selected by one logical bit. -/
def constantConfiguration (A : Type*) (bit : Fin 2) : A → Fin 2 :=
  fun _ => bit

/-- The two-by-two logical coefficient matrix of a GHZ state across a cut. -/
def ghzLogicalCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The GHZ amplitude on the full configuration spaces of the two sides of a cut. -/
noncomputable def ghzCutAmplitude {A B : Type*}
    (left : A → Fin 2) (right : B → Fin 2) : ℂ := by
  classical
  exact if left = constantConfiguration A 0 ∧ right = constantConfiguration B 0 then
      (Real.sqrt 2 : ℂ)⁻¹
    else if left = constantConfiguration A 1 ∧ right = constantConfiguration B 1 then
      (Real.sqrt 2 : ℂ)⁻¹
    else 0

/-- The reduced density matrix on the logical all-zero/all-one sector of either cut side. -/
def ghzReducedLogicalDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  ghzLogicalCoefficient * ghzLogicalCoefficient.conjTranspose

/-- The entropy of the two explicit Schmidt weights. -/
def ghzCutEntropy : ℝ :=
  ∑ _ : Fin 2, -(1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  have realIdentity := congrArg (fun value : ℝ => (value : ℂ))
    TsirelsonInequality.sqrt_two_inv_mul_self
  simpa using realIdentity

private theorem constant_configuration_injective (A : Type*) [Nonempty A] :
    Function.Injective (constantConfiguration A) := by
  intro first second equalConfigurations
  exact congrFun equalConfigurations (Classical.choice inferInstance)

private theorem ghz_logical_coefficient_normalized :
    (∑ i, ∑ j, star (ghzLogicalCoefficient i j) * ghzLogicalCoefficient i j) = 1 := by
  norm_num [ghzLogicalCoefficient, Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]

private theorem ghz_logical_coefficient_rank :
    Matrix.rank ghzLogicalCoefficient = 2 := by
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hdet : Matrix.det ghzLogicalCoefficient ≠ 0 := by
    simp [ghzLogicalCoefficient, Matrix.det_fin_two, hsqrt]
  simpa using Matrix.rank_of_det_ne_zero hdet

private theorem ghz_reduced_logical_density :
    ghzReducedLogicalDensity = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ghzReducedLogicalDensity, ghzLogicalCoefficient, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]

private theorem ghz_cut_entropy_eq_log_two :
    ghzCutEntropy = Real.log 2 := by
  rw [ghzCutEntropy, Fin.sum_univ_two]
  norm_num
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- For arbitrary finite nonempty cut sides, the two global constant configurations are distinct
on each side and carry the whole normalized GHZ state. Its logical coefficient matrix has rank
two, its reduced density is one half of the identity, and its two equal Schmidt weights have
entropy `log 2`. -/
theorem ghz_entangled_across_every_nontrivial_cut
    (A B : Type*) [Nonempty A] [Nonempty B] :
    Function.Injective (constantConfiguration A) ∧
      Function.Injective (constantConfiguration B) ∧
      (∀ i j,
        ghzCutAmplitude (constantConfiguration A i) (constantConfiguration B j) =
          ghzLogicalCoefficient i j) ∧
      (∀ left right, ghzCutAmplitude left right ≠ 0 →
        ∃ bit, left = constantConfiguration A bit ∧
          right = constantConfiguration B bit) ∧
      (∑ i, ∑ j, star (ghzLogicalCoefficient i j) * ghzLogicalCoefficient i j) = 1 ∧
      Matrix.rank ghzLogicalCoefficient = 2 ∧
      ghzReducedLogicalDensity = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ i, ghzReducedLogicalDensity i i = 1 / 2) ∧
      ghzCutEntropy = Real.log 2 := by
  classical
  refine ⟨constant_configuration_injective A, constant_configuration_injective B, ?_, ?_,
    ghz_logical_coefficient_normalized, ghz_logical_coefficient_rank,
    ghz_reduced_logical_density, ?_, ghz_cut_entropy_eq_log_two⟩
  · intro i j
    have hA : constantConfiguration A 0 ≠ constantConfiguration A 1 :=
      (constant_configuration_injective A).ne (by decide)
    have hB : constantConfiguration B 0 ≠ constantConfiguration B 1 :=
      (constant_configuration_injective B).ne (by decide)
    fin_cases i <;> fin_cases j <;>
      simp [ghzCutAmplitude, ghzLogicalCoefficient, hA, hB, Ne.symm hA, Ne.symm hB]
  · intro left right nonzeroAmplitude
    by_cases hzero : left = constantConfiguration A 0 ∧ right = constantConfiguration B 0
    · exact ⟨0, hzero⟩
    by_cases hone : left = constantConfiguration A 1 ∧ right = constantConfiguration B 1
    · exact ⟨1, hone⟩
    exact (nonzeroAmplitude (by simp [ghzCutAmplitude, hzero, hone])).elim
  · intro i
    rw [ghz_reduced_logical_density]
    simp

#print axioms ghz_entangled_across_every_nontrivial_cut

end D5.S3.Quantum.GhzBipartitionEntanglement
