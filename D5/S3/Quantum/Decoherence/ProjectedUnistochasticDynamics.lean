/- GID: D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Projected unitary dynamics induces a doubly stochastic transition law. -/

import D5.S3.Weil.ZetaLinear.VonNeumann

/-!
# Projected unitary dynamics

A unitary matrix is written in measurement-basis coordinates.  Conjugation followed by
diagonal readout sends every already-diagonal state to another diagonal state, and its diagonal
weights evolve by the squared entry norms of the unitary.
-/

noncomputable section

open Matrix Finset

namespace D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one projector onto a coordinate of the measurement basis. -/
def basisProjector (j : ι) : Matrix ι ι ℂ :=
  Matrix.single j j 1

/-- The density matrix whose measurement-basis weights are `p`. -/
def diagonalState (p : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun j => (p j : ℂ)

/-- Projection of a matrix onto its measurement-basis diagonal. -/
def projectiveReadout (rho : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (Matrix.diag rho)

/-- Unitary evolution in measurement-basis coordinates. -/
def unitaryEvolution (U rho : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U * rho * star U

/-- One unitary evolution followed by projective readout. -/
def projectedStep (U rho : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  projectiveReadout (unitaryEvolution U rho)

/-- The post-projection orbit, indexed with the first projected state at zero. -/
def projectedOrbit (U : Matrix ι ι ℂ) (initialWeights : ι → ℝ) :
    ℕ → Matrix ι ι ℂ
  | 0 => diagonalState initialWeights
  | n + 1 => projectedStep U (projectedOrbit U initialWeights n)

/-- Probabilities read from the diagonal of the post-projection orbit. -/
def projectedWeights (U : Matrix ι ι ℂ) (initialWeights : ι → ℝ)
    (n : ℕ) (j : ι) : ℝ :=
  Complex.re (projectedOrbit U initialWeights n j j)

/-- The squared-amplitude transition matrix of `U`. -/
def transitionMatrix (U : Matrix ι ι ℂ) : Matrix ι ι ℝ :=
  RHLinalg.normSqMatrix U

private theorem diagonal_state_eq_projector_sum (p : ι → ℝ) :
    diagonalState p = ∑ j, (p j : ℂ) • basisProjector j := by
  ext k l
  by_cases hkl : k = l
  · subst l
    rw [Matrix.sum_apply, Finset.sum_eq_single k]
    · simp [diagonalState, basisProjector]
    · intro j _ hj
      simp [basisProjector, hj]
    · simp
  · simp only [Matrix.sum_apply, diagonalState, Matrix.diagonal_apply_ne _ hkl,
      basisProjector, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
      mul_ite, mul_one, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro j _
    simp only [ite_eq_right_iff]
    intro hj
    exact (hkl (hj.1.symm.trans hj.2)).elim

private theorem projected_step_diagonal_state (U : Matrix ι ι ℂ) (p : ι → ℝ) :
    projectedStep U (diagonalState p) =
      diagonalState (transitionMatrix U *ᵥ p) := by
  ext k l
  by_cases hkl : k = l
  · subst l
    simp only [projectedStep, projectiveReadout, unitaryEvolution, diagonalState,
      Matrix.diagonal_apply_eq, Matrix.diag_apply, transitionMatrix,
      RHLinalg.normSqMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct]
    change
      (U * Matrix.diagonal (fun j => (p j : ℂ)) * star U) k k =
        ((∑ j, ‖U k j‖ ^ 2 * p j : ℝ) : ℂ)
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply, RCLike.star_def]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    calc
      U k j * (p j : ℂ) * starRingEnd ℂ (U k j) =
          (U k j * starRingEnd ℂ (U k j)) * (p j : ℂ) := by ring
      _ = ((‖U k j‖ : ℂ) ^ 2) * (p j : ℂ) := by
        rw [RCLike.mul_conj]
        rfl
  · simp [projectedStep, projectiveReadout, diagonalState, hkl]

private theorem projected_orbit_diagonal
    (U : Matrix ι ι ℂ) (initialWeights : ι → ℝ) :
    ∀ n, projectedOrbit U initialWeights n =
      diagonalState (projectedWeights U initialWeights n) := by
  intro n
  induction n with
  | zero =>
      ext k l
      by_cases hkl : k = l
      · subst l
        simp [projectedOrbit, projectedWeights, diagonalState]
      · simp [projectedOrbit, projectedWeights, diagonalState, hkl]
  | succ n ih =>
      rw [projectedOrbit, ih, projected_step_diagonal_state]
      ext k l
      by_cases hkl : k = l
      · subst l
        unfold projectedWeights
        rw [projectedOrbit, ih, projected_step_diagonal_state]
        simp [diagonalState]
      · simp [diagonalState, hkl]

/-- From the first projected state onward, the density matrix is a mixture of basis projectors;
the squared-amplitude transition matrix is doubly stochastic and advances all weights by matrix
multiplication. -/
theorem projected_dynamics_is_unistochastic
    (U : Matrix ι ι ℂ) (initialWeights : ι → ℝ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ n, projectedOrbit U initialWeights n =
      ∑ j, (projectedWeights U initialWeights n j : ℂ) • basisProjector j) ∧
    (∀ k j, transitionMatrix U k j = ‖U k j‖ ^ 2) ∧
    transitionMatrix U ∈ doublyStochastic ℝ ι ∧
    (∀ n, projectedWeights U initialWeights (n + 1) =
      transitionMatrix U *ᵥ projectedWeights U initialWeights n) := by
  refine ⟨fun n => ?_, fun _ _ => rfl, ?_, fun n => ?_⟩
  · rw [projected_orbit_diagonal]
    exact diagonal_state_eq_projector_sum _
  · exact RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hU
  · funext k
    unfold projectedWeights
    rw [projectedOrbit, projected_orbit_diagonal, projected_step_diagonal_state]
    simp [diagonalState]

#print axioms projected_dynamics_is_unistochastic

end D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
