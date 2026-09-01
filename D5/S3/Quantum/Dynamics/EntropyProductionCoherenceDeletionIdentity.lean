/- GID: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify entropy production under repeated unitary evolution and basis dephasing. -/

import D5.S3.Divergence.GrandmotherTheorem
import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance (priority := 2000) : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAddCommGroup

local instance (priority := 2000) : NormedSpace ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedSpace

local instance (priority := 2000) : NormedRing (Matrix n n ℂ) :=
  Matrix.instL2OpNormedRing

local instance (priority := 2000) : NormedAlgebra ℂ (Matrix n n ℂ) :=
  Matrix.instL2OpNormedAlgebra

private lemma densityMatrix_posSemidef (rho : DensityState n) :
    (densityMatrix rho).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1

private def diagonalStarAlgHom : (n -> ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toAlgHom := Matrix.diagonalAlgHom ℂ
  map_star' a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.star_apply]
    · simp [Matrix.star_apply, hij, Ne.symm hij]

private lemma cfc_log_diagonal (a : n -> ℝ) :
    CFC.log (Matrix.diagonal fun i => (a i : ℂ)) =
      Matrix.diagonal fun i => (Real.log (a i) : ℂ) := by
  letI : ContinuousFunctionalCalculus ℝ (n -> ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let z : n -> ℂ := fun i => (a i : ℂ)
  have hz : IsSelfAdjoint z := by
    ext i
    simp [z, Pi.star_apply]
  have hDiagonal : IsSelfAdjoint (diagonalStarAlgHom z) := by
    exact hz.map (diagonalStarAlgHom (n := n))
  have hLog : ContinuousOn Real.log (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    apply Set.Finite.continuousOn
    exact Set.finite_iUnion fun i =>
      (Set.finite_singleton (a i)).subset
        (CFC.spectrum_algebraMap_subset (A := ℂ) (a i))
  have hmap := (diagonalStarAlgHom (n := n)).map_cfc
    (R := ℝ) Real.log z hLog
    (diagonalStarAlgHom (n := n)).toLinearMap.continuous_of_finiteDimensional hz hDiagonal
  rw [CFC.log]
  change cfc Real.log (diagonalStarAlgHom z) = _
  rw [← hmap]
  change diagonalStarAlgHom (cfc Real.log z) = _
  have hLogPi : ContinuousOn Real.log (⋃ i, spectrum ℝ (z i)) := by
    rwa [Pi.spectrum_eq] at hLog
  rw [cfc_map_pi (S := ℂ) Real.log z hLogPi hz (fun i => by
    change star (a i : ℂ) = (a i : ℂ)
    simp)]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagonalStarAlgHom, Matrix.diagonal_apply_eq]
    simpa [z] using (cfc_algebraMap (R := ℝ) (A := ℂ) (a i) Real.log)
  · simp [diagonalStarAlgHom, hij]

private lemma diagonal_entry_eq_real (rho : DensityState n) (i : n) :
    densityMatrix rho i i = ((densityMatrix rho i i).re : ℂ) := by
  have hNonneg : 0 ≤ densityMatrix rho i i :=
    (densityMatrix_posSemidef rho).diag_nonneg
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp hNonneg).2.symm

private lemma cfc_log_projectiveReadout (rho : DensityState n) :
    CFC.log (projectiveReadout (densityMatrix rho)) =
      Matrix.diagonal fun i => (Real.log (densityMatrix rho i i).re : ℂ) := by
  have hReadout :
      projectiveReadout (densityMatrix rho) =
        Matrix.diagonal fun i => ((densityMatrix rho i i).re : ℂ) := by
    unfold projectiveReadout
    congr 1
    funext i
    exact diagonal_entry_eq_real rho i
  rw [hReadout, cfc_log_diagonal]

/-- Unitary conjugation of a density state, using the existing matrix evolution primitive. -/
noncomputable def unitaryConjugateState (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (rho : DensityState n) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (unitaryEvolution U (densityMatrix rho)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    rw [Matrix.nonneg_iff_posSemidef]
    simpa [unitaryEvolution, Matrix.star_eq_conjTranspose] using
      (densityMatrix_posSemidef rho).mul_mul_conjTranspose_same U
  · have hStar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    change Matrix.trace (unitaryEvolution U (densityMatrix rho)) = 1
    rw [unitaryEvolution, Matrix.trace_mul_cycle, hStar, Matrix.one_mul]
    exact rho.2.2

/-- Basis pinching of a density state, using the existing projective readout primitive. -/
noncomputable def basisPinchingState (rho : DensityState n) : DensityState n := by
  refine ⟨CStarMatrix.ofMatrix (projectiveReadout (densityMatrix rho)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    rw [Matrix.nonneg_iff_posSemidef, projectiveReadout,
      Matrix.posSemidef_diagonal_iff]
    exact fun i => (densityMatrix_posSemidef rho).diag_nonneg
  · change Matrix.trace (projectiveReadout (densityMatrix rho)) = 1
    calc
      Matrix.trace (projectiveReadout (densityMatrix rho)) =
          Matrix.trace (densityMatrix rho) := by
        simp only [projectiveReadout, Matrix.trace, Matrix.diag_diagonal]
      _ = 1 := by
        change Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1
        exact rho.2.2

private lemma sum_mul_log_mulVec_le (M : Matrix n n ℝ)
    (hM : M ∈ doublyStochastic ℝ n) (x : n -> ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, (M *ᵥ x) i * Real.log ((M *ᵥ x) i) ≤
      ∑ i, x i * Real.log (x i) := by
  have hRow (i : n) :
      (M *ᵥ x) i * Real.log ((M *ᵥ x) i) ≤
        ∑ j, M i j * (x j * Real.log (x j)) := by
    simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using
      Real.convexOn_mul_log.map_sum_le
        (t := Finset.univ) (w := M i) (p := x)
        (fun j _ => nonneg_of_mem_doublyStochastic hM)
        (sum_row_of_mem_doublyStochastic hM i)
        (fun j _ => hx j)
  calc
    ∑ i, (M *ᵥ x) i * Real.log ((M *ᵥ x) i)
        ≤ ∑ i, ∑ j, M i j * (x j * Real.log (x j)) :=
      Finset.sum_le_sum fun i _ => hRow i
    _ = ∑ j, x j * Real.log (x j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hM j, one_mul]

private lemma diagonal_eq_normSq_mulVec (rho : DensityState n) :
    (fun i => (densityMatrix rho i i).re) =
      RHLinalg.normSqMatrix
        ((densityMatrix_posSemidef rho).isHermitian.eigenvectorUnitary :
          Matrix n n ℂ) *ᵥ
          (densityMatrix_posSemidef rho).isHermitian.eigenvalues := by
  funext i
  let hRho := (densityMatrix_posSemidef rho).isHermitian
  let V : Matrix n n ℂ := hRho.eigenvectorUnitary
  change (densityMatrix rho i i).re =
    (RHLinalg.normSqMatrix (hRho.eigenvectorUnitary : Matrix n n ℂ) *ᵥ
      hRho.eigenvalues) i
  conv_lhs =>
    rw [hRho.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply,
    RCLike.star_def, Matrix.mulVec, dotProduct,
    RHLinalg.normSqMatrix, Matrix.of_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change
    (V i j * (hRho.eigenvalues j : ℂ) * starRingEnd ℂ (V i j)).re =
      ‖V i j‖ ^ 2 * hRho.eigenvalues j
  rw [show
    (V i j * (hRho.eigenvalues j : ℂ) * starRingEnd ℂ (V i j)).re =
      ‖V i j‖ ^ 2 * hRho.eigenvalues j by
        rw [show V i j * (hRho.eigenvalues j : ℂ) * starRingEnd ℂ (V i j) =
          (V i j * starRingEnd ℂ (V i j)) * (hRho.eigenvalues j : ℂ) by ring,
          Complex.mul_conj]
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [Complex.normSq_eq_norm_sq]]

private lemma trace_mul_cfc_eq_sum (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (f : ℝ -> ℝ) :
    (Matrix.trace (A * cfc f A)).re =
      ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  let V : Matrix n n ℂ := hA.eigenvectorUnitary
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let F : Matrix n n ℂ := Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))
  have hStar : star V * V = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hAeq : A = V * D * star V := by
    simpa [V, D, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.spectral_theorem
  have hFeq : cfc f A = V * F * star V := by
    rw [hA.cfc_eq]
    rfl
  have hTraceEq :
      (Matrix.trace (A * cfc f A)).re =
        (Matrix.trace ((V * D * star V) * (V * F * star V))).re := by
    exact congrArg (fun X : Matrix n n ℂ => (Matrix.trace X).re)
      (congrArg₂ (· * ·) hAeq hFeq)
  rw [hTraceEq]
  have hProduct :
      (V * D * star V) * (V * F * star V) = V * (D * F) * star V := by
    calc
      (V * D * star V) * (V * F * star V) =
          V * D * (star V * V) * F * star V := by noncomm_ring
      _ = V * (D * F) * star V := by
        rw [hStar]
        simp only [Matrix.mul_one]
        noncomm_ring
  rw [hProduct, Matrix.trace_mul_cycle, hStar, one_mul]
  simp [D, F, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

private lemma cfc_log_densityMatrix (rho : DensityState n) :
    CFC.log rho.1 = CStarMatrix.ofMatrix (CFC.log (densityMatrix rho)) := rfl

private lemma von_neumann_entropy_eq_eigenvalue_sum (rho : DensityState n) :
    vonNeumannEntropy rho =
      -(∑ i, (densityMatrix_posSemidef rho).isHermitian.eigenvalues i *
        Real.log ((densityMatrix_posSemidef rho).isHermitian.eigenvalues i)) := by
  unfold vonNeumannEntropy
  rw [cfc_log_densityMatrix]
  change -(Matrix.trace
    (densityMatrix rho * CFC.log (densityMatrix rho))).re = _
  rw [CFC.log]
  rw [trace_mul_cfc_eq_sum (densityMatrix rho)
    (densityMatrix_posSemidef rho).isHermitian Real.log]

private lemma von_neumann_entropy_basisPinchingState (rho : DensityState n) :
    vonNeumannEntropy (basisPinchingState rho) =
      -(∑ i, (densityMatrix rho i i).re * Real.log (densityMatrix rho i i).re) := by
  unfold vonNeumannEntropy
  rw [cfc_log_densityMatrix]
  change -(Matrix.trace
    (projectiveReadout (densityMatrix rho) *
      CFC.log (projectiveReadout (densityMatrix rho)))).re = _
  rw [cfc_log_projectiveReadout]
  simp [Matrix.trace, projectiveReadout]

private lemma cfc_log_basisPinchingState (rho : DensityState n) :
    CFC.log (basisPinchingState rho).1 =
      CStarMatrix.ofMatrix
        (Matrix.diagonal fun i =>
          (Real.log (densityMatrix rho i i).re : ℂ)) := by
  rw [cfc_log_densityMatrix]
  change CStarMatrix.ofMatrix
    (CFC.log (projectiveReadout (densityMatrix rho))) = _
  rw [cfc_log_projectiveReadout]

private lemma trace_mul_log_basisPinchingState (rho : DensityState n) :
    Matrix.trace (rho.1 * CFC.log (basisPinchingState rho).1) =
      Matrix.trace
        ((basisPinchingState rho).1 * CFC.log (basisPinchingState rho).1) := by
  rw [cfc_log_basisPinchingState]
  change Matrix.trace
      (densityMatrix rho * Matrix.diagonal (fun i =>
        (Real.log (densityMatrix rho i i).re : ℂ))) =
    Matrix.trace
      (projectiveReadout (densityMatrix rho) * Matrix.diagonal (fun i =>
        (Real.log (densityMatrix rho i i).re : ℂ)))
  simp [Matrix.trace, projectiveReadout, Matrix.mul_diagonal]

private lemma pinching_entropy_gain_eq_relative_entropy (rho : DensityState n) :
    vonNeumannEntropy (basisPinchingState rho) - vonNeumannEntropy rho =
      quantumRelativeEntropy rho (basisPinchingState rho) := by
  have hCross := trace_mul_log_basisPinchingState rho
  rw [quantum_relative_entropy_eq_neg_entropy_sub_cross]
  unfold vonNeumannEntropy
  rw [hCross]
  ring

private lemma quantumRelativeEntropy_basisPinchingState_nonneg (rho : DensityState n) :
    0 ≤ quantumRelativeEntropy rho (basisPinchingState rho) := by
  rw [← pinching_entropy_gain_eq_relative_entropy rho,
    von_neumann_entropy_basisPinchingState, von_neumann_entropy_eq_eigenvalue_sum]
  let hRho := densityMatrix_posSemidef rho
  let M := RHLinalg.normSqMatrix
    (hRho.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  have hM : M ∈ doublyStochastic ℝ n :=
    RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
      hRho.isHermitian.eigenvectorUnitary.2
  have hConvex := sum_mul_log_mulVec_le M hM hRho.isHermitian.eigenvalues
    hRho.eigenvalues_nonneg
  have hDiag : (fun i => (densityMatrix rho i i).re) =
      M *ᵥ hRho.isHermitian.eigenvalues := by
    simpa [M, hRho] using diagonal_eq_normSq_mulVec rho
  have hConvex' :
      ∑ i, (densityMatrix rho i i).re * Real.log (densityMatrix rho i i).re ≤
        ∑ i, hRho.isHermitian.eigenvalues i *
          Real.log (hRho.isHermitian.eigenvalues i) := by
    simpa only [congrFun hDiag] using hConvex
  linarith

private lemma cfc_log_unitaryConjugateState (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (rho : DensityState n) :
    CFC.log (unitaryConjugateState U hU rho).1 =
      CStarMatrix.ofMatrix U * CFC.log rho.1 *
        star (CStarMatrix.ofMatrix U) := by
  let u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
  have hRho := densityMatrix_posSemidef rho
  have hLog : ContinuousOn Real.log (spectrum ℝ (densityMatrix rho)) :=
    (Set.toFinite (spectrum ℝ (densityMatrix rho))).continuousOn Real.log
  have hMap := StarAlgHomClass.map_cfc
    (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) Real.log (densityMatrix rho)
    (hf := hLog)
    (hφ := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u).toAlgEquiv.toLinearMap
      |>.continuous_of_finiteDimensional)
    (ha := hRho.isHermitian)
    (hφa := by
      have hSelf : IsSelfAdjoint (densityMatrix rho) := hRho.isHermitian
      exact hSelf.map (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u))
  rw [CFC.log]
  change cfc Real.log (unitaryEvolution U (densityMatrix rho)) =
    U * cfc Real.log (densityMatrix rho) * star U
  simpa [u, unitaryEvolution,
    Unitary.conjStarAlgAut_apply] using hMap.symm

private lemma von_neumann_entropy_unitaryConjugateState (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (rho : DensityState n) :
    vonNeumannEntropy (unitaryConjugateState U hU rho) =
      vonNeumannEntropy rho := by
  have hStarC :
      star (CStarMatrix.ofMatrix U) * CStarMatrix.ofMatrix U = 1 := by
    change star U * U = 1
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  unfold vonNeumannEntropy
  change
    -(Matrix.trace
      ((unitaryConjugateState U hU rho).1 *
        CFC.log (unitaryConjugateState U hU rho).1)).re =
        -(Matrix.trace (rho.1 * CFC.log rho.1)).re
  rw [cfc_log_unitaryConjugateState U hU rho]
  change
    -(Matrix.trace
      ((U * densityMatrix rho * star U) *
        (U * CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.log rho.1) * star U))).re =
      -(Matrix.trace
        (densityMatrix rho *
          CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.log rho.1))).re
  have hProduct :
      (U * densityMatrix rho * star U) *
          (U * CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.log rho.1) * star U) =
        U * (densityMatrix rho *
          CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.log rho.1)) * star U := by
    calc
      _ = U * densityMatrix rho * (star U * U) *
          CStarMatrix.ofMatrixStarAlgEquiv.symm (CFC.log rho.1) * star U := by
        noncomm_ring
      _ = _ := by
        change star U * U = 1 at hStarC
        rw [hStarC]
        simp only [Matrix.mul_one]
        noncomm_ring
  rw [hProduct, Matrix.trace_mul_cycle]
  change star U * U = 1 at hStarC
  rw [hStarC, Matrix.one_mul]

/-- Repeated unitary evolution followed by basis pinching produces exactly the deleted
coherence as entropy, and the finite entropy gain is the sum of those nonnegative taxes. -/
theorem entropy_production_coherence_deletion_identity
    (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (rho : ℕ → DensityState n)
    (hStep : ∀ k,
      rho (k + 1) = basisPinchingState (unitaryConjugateState U hU (rho k))) :
    (∀ k,
      vonNeumannEntropy (rho (k + 1)) - vonNeumannEntropy (rho k) =
          quantumRelativeEntropy
            (unitaryConjugateState U hU (rho k))
            (basisPinchingState (unitaryConjugateState U hU (rho k))) ∧
        0 ≤ quantumRelativeEntropy
          (unitaryConjugateState U hU (rho k))
          (basisPinchingState (unitaryConjugateState U hU (rho k)))) ∧
      (∀ N,
        vonNeumannEntropy (rho N) - vonNeumannEntropy (rho 0) =
          ∑ k ∈ Finset.range N,
            quantumRelativeEntropy
              (unitaryConjugateState U hU (rho k))
              (basisPinchingState (unitaryConjugateState U hU (rho k)))) := by
  have hOneStep (k : ℕ) :
      vonNeumannEntropy (rho (k + 1)) - vonNeumannEntropy (rho k) =
        quantumRelativeEntropy
          (unitaryConjugateState U hU (rho k))
          (basisPinchingState (unitaryConjugateState U hU (rho k))) := by
    rw [hStep k]
    calc
      vonNeumannEntropy
          (basisPinchingState (unitaryConjugateState U hU (rho k))) -
            vonNeumannEntropy (rho k) =
          vonNeumannEntropy
              (basisPinchingState (unitaryConjugateState U hU (rho k))) -
            vonNeumannEntropy (unitaryConjugateState U hU (rho k)) := by
              rw [von_neumann_entropy_unitaryConjugateState]
      _ = quantumRelativeEntropy
            (unitaryConjugateState U hU (rho k))
            (basisPinchingState (unitaryConjugateState U hU (rho k))) :=
        pinching_entropy_gain_eq_relative_entropy _
  constructor
  · intro k
    exact ⟨hOneStep k,
      quantumRelativeEntropy_basisPinchingState_nonneg
        (unitaryConjugateState U hU (rho k))⟩
  · intro N
    rw [← Finset.sum_range_sub (fun k ↦ vonNeumannEntropy (rho k)) N]
    apply Finset.sum_congr rfl
    intro k _
    exact hOneStep k

#print axioms entropy_production_coherence_deletion_identity

end D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
