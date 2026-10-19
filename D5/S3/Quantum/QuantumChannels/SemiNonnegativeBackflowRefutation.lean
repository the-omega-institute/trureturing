/- GID: D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim; result=D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result; claim=D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim
   digest: A non-SP semi-nonnegative qutrit map doubles trace distance in a Kraus context. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (of_kraus)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (krausApply IsKrausChannel)

namespace D5.S3.Quantum.QuantumChannels.SemiNonnegativeBackflowRefutation

/-- Hermiticity and trace preservation for a complex-linear matrix map. -/
def IsHPTP {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ X, Ψ Xᴴ = (Ψ X)ᴴ) ∧ ∀ X, trace (Ψ X) = trace X

/-- Some positive-definite density has a positive-definite density image. -/
def IsSemiPositive {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ ρ, IsDensity ρ ∧ ρ.PosDef ∧ IsDensity (Ψ ρ) ∧ (Ψ ρ).PosDef

/-- Some density has a density image. -/
def IsSemiNonnegative {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ ρ, IsDensity ρ ∧ IsDensity (Ψ ρ)

/-- The matrix trace distance, using the canonical trace norm. -/
def traceDistance {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- The no-backflow conjunct of the higher-dimensional non-SP SNTP conjecture. -/
def claim : Prop :=
  ∀ (d : ℕ) (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ),
    IsHPTP Ψ ∧ IsSemiNonnegative Ψ ∧ ¬ IsSemiPositive Ψ →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (K : ι → Matrix (Fin d) (Fin d) ℂ) (L : κ → Matrix (Fin d) (Fin d) ℂ),
      IsKrausChannel K → IsKrausChannel L →
      (∀ X, Ψ (krausApply K X) = krausApply L X) →
      ∀ σ₁ σ₂, IsDensity σ₁ → IsDensity σ₂ →
        traceDistance (krausApply L σ₁) (krausApply L σ₂) ≤
          traceDistance (krausApply K σ₁) (krausApply K σ₂)

private def psi : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun X :=
    !![2 * X 0 0 - (X 0 0 + X 1 1) / 2 + X 2 2, 2 * X 0 1, X 0 2;
       2 * X 1 0, 2 * X 1 1 - (X 0 0 + X 1 1) / 2 + X 2 2, X 1 2;
       X 2 0, X 2 1, -X 2 2]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem psi_hptp : IsHPTP psi := by
  constructor
  · intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [psi.eq_1, conjTranspose_apply]
  · intro X
    simp [psi.eq_1, trace, Fin.sum_univ_three]
    ring

private def faceState : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 2, 1 / 2, 0]

private theorem face_density : IsDensity faceState := by
  constructor
  · change (diagonal ![(1 / 2 : ℂ), 1 / 2, 0]).PosSemidef
    rw [posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num [Complex.le_def, Matrix.cons_val_two, vecHead, vecTail]
  · norm_num [faceState.eq_1, trace, Fin.sum_univ_three, Matrix.cons_val_two, vecHead, vecTail]

private theorem psi_face : psi faceState = faceState := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [psi.eq_1, faceState.eq_1, Matrix.diagonal,
    Matrix.cons_val_two, vecHead, vecTail, Fin.ext_iff]

private theorem psi_sn : IsSemiNonnegative psi :=
  ⟨faceState, face_density, psi_face.symm ▸ face_density⟩

private theorem psi_not_sp : ¬ IsSemiPositive psi := by
  rintro ⟨ρ, _, hpos, hout, _⟩
  have hn : 0 ≤ -(ρ 2 2) := by
    simpa [psi.eq_1] using (hout.1.diag_nonneg (i := 2))
  exact (not_le_of_gt (hpos.diag_pos (i := 2))) (neg_nonneg.mp hn)

private def proj : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1, 1, 0]

private def xiKraus : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![proj, single 0 2 (1 / 2), single 0 2 (1 / 2),
    single 1 2 (1 / 2), single 1 2 (1 / 2)]

private def phiKraus : Fin 10 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![faceState, faceState, single 0 2 (1 / 2), single 1 2 (1 / 2),
    single 0 0 (1 / 2), single 0 1 (1 / 2), single 0 2 (1 / 2),
    single 1 0 (1 / 2), single 1 1 (1 / 2), single 1 2 (1 / 2)]

private def xi (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![X 0 0 + X 2 2 / 2, X 0 1, 0;
     X 1 0, X 1 1 + X 2 2 / 2, 0;
     0, 0, 0]

private def phi (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![X 0 0 / 2 + X 2 2 / 4 + (X 0 0 + X 1 1 + X 2 2) / 4, X 0 1 / 2, 0;
     X 1 0 / 2, X 1 1 / 2 + X 2 2 / 4 + (X 0 0 + X 1 1 + X 2 2) / 4, 0;
     0, 0, 0]

private theorem xi_normalized : IsKrausChannel xiKraus := by
  unfold IsKrausChannel
  simp only [xiKraus.eq_1, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [proj.eq_1, diagonal_conjTranspose, diagonal_mul_diagonal, Matrix.single,
      Matrix.cons_val_two, vecHead, vecTail, Fin.ext_iff, map_ofNat]

private theorem phi_normalized : IsKrausChannel phiKraus := by
  unfold IsKrausChannel
  simp only [phiKraus.eq_1, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.conjTranspose_single, Matrix.single_mul_single_same]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [faceState.eq_1, diagonal_conjTranspose, diagonal_mul_diagonal, Matrix.single,
      Matrix.cons_val_two, vecHead, vecTail, Fin.ext_iff, map_ofNat]

private theorem xi_action (X : Matrix (Fin 3) (Fin 3) ℂ) : krausApply xiKraus X = xi X := by
  rw [krausApply.eq_1]
  simp only [of_kraus, xiKraus.eq_1, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.conjTranspose_single,
      Matrix.single_mul_mul_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [proj.eq_1, xi.eq_1, diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.single, Matrix.cons_val_two, vecHead, vecTail, Fin.ext_iff,
        map_ofNat] <;> ring

private theorem phi_action (X : Matrix (Fin 3) (Fin 3) ℂ) : krausApply phiKraus X = phi X := by
  rw [krausApply.eq_1]
  simp only [of_kraus, phiKraus.eq_1, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.conjTranspose_single,
      Matrix.single_mul_mul_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [faceState.eq_1, phi.eq_1, diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.single, Matrix.cons_val_two, vecHead, vecTail, Fin.ext_iff,
        map_ofNat] <;> ring

private theorem context (X : Matrix (Fin 3) (Fin 3) ℂ) :
    psi (krausApply phiKraus X) = krausApply xiKraus X := by
  rw [phi_action, xi_action]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psi.eq_1, phi.eq_1, xi.eq_1] <;> ring

private def sigmaPlus : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![5 / 8, 1 / 8, 1 / 4]
private def sigmaMinus : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1 / 8, 5 / 8, 1 / 4]

private theorem inputs_density : IsDensity sigmaPlus ∧ IsDensity sigmaMinus := by
  constructor
  · constructor
    · change (diagonal ![(5 / 8 : ℂ), 1 / 8, 1 / 4]).PosSemidef
      rw [posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> norm_num [Complex.le_def, Matrix.cons_val_two, vecHead, vecTail]
    · norm_num [sigmaPlus.eq_1, trace, Fin.sum_univ_three, Matrix.cons_val_two, vecHead, vecTail]
  · constructor
    · change (diagonal ![(1 / 8 : ℂ), 5 / 8, 1 / 4]).PosSemidef
      rw [posSemidef_diagonal_iff]
      intro i
      fin_cases i <;> norm_num [Complex.le_def, Matrix.cons_val_two, vecHead, vecTail]
    · norm_num [sigmaMinus.eq_1, trace, Fin.sum_univ_three, Matrix.cons_val_two, vecHead, vecTail]

private theorem distance_before : traceDistance (phi sigmaPlus) (phi sigmaMinus) = 1 / 4 := by
  unfold traceDistance
  rw [show phi sigmaPlus - phi sigmaMinus =
      diagonal (fun i => ((![1 / 4, -(1 / 4), 0] : Fin 3 → ℝ) i : ℂ)) by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [phi.eq_1, sigmaPlus.eq_1, sigmaMinus.eq_1,
      Matrix.cons_val_two, vecHead, vecTail]]
  rw [D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, vecHead, vecTail]

private theorem distance_after : traceDistance (xi sigmaPlus) (xi sigmaMinus) = 1 / 2 := by
  unfold traceDistance
  rw [show xi sigmaPlus - xi sigmaMinus =
      diagonal (fun i => ((![1 / 2, -(1 / 2), 0] : Fin 3 → ℝ) i : ℂ)) by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [xi.eq_1, sigmaPlus.eq_1, sigmaMinus.eq_1,
      Matrix.cons_val_two, vecHead, vecTail]]
  rw [D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation.diagonal_norm]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, vecHead, vecTail]

/-- A single normalized qutrit context increases trace distance from 1/4 to 1/2. -/
theorem result : ¬ claim := by
  intro h
  have hdist := h 3 psi ⟨psi_hptp, psi_sn, psi_not_sp⟩
    (Fin 10) (Fin 5) phiKraus xiKraus phi_normalized xi_normalized context
    sigmaPlus sigmaMinus inputs_density.1 inputs_density.2
  rw [xi_action, xi_action, phi_action, phi_action, distance_after, distance_before] at hdist
  norm_num at hdist

end D5.S3.Quantum.QuantumChannels.SemiNonnegativeBackflowRefutation
