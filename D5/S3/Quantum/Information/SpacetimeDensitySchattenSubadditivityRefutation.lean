/- GID: D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.claim; result=D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.result; claim=D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation.claim
   digest: A rational three-qubit state refutes temporal Schatten subadditivity. -/

import D5.S3.Quantum.Schatten.Holder
import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation
import D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option linter.style.longLine false

open scoped BigOperators Matrix Kronecker ComplexOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Information.SpacetimeDensitySchattenSubadditivityRefutation

def claim : Prop :=
  ∀ (a abar b bbar : Type) [Fintype a] [DecidableEq a] [Fintype abar] [DecidableEq abar]
    [Fintype b] [DecidableEq b] [Fintype bbar] [DecidableEq bbar]
    (ρ : Matrix (a × abar) (a × abar) ℂ) (U : Matrix (b × bbar) (a × abar) ℂ)
    (T : Matrix (a × b) (a × b) ℂ) (p : ℝ),
    ρ.PosSemidef → ρ.trace = 1 → Uᴴ * U = 1 → U * Uᴴ = 1 →
    (∀ (OA : Matrix a a ℂ) (OB : Matrix b b ℂ),
      (T * (OA ⊗ₖ OB)).trace =
        (ρ * (OA ⊗ₖ (1 : Matrix abar abar ℂ)) * Uᴴ * (OB ⊗ₖ (1 : Matrix bbar bbar ℂ)) * U).trace) →
    1 < p →
    schattenNorm (partialTraceLeft T) p + schattenNorm (partialTraceRight T) p ≤ 1 + schattenNorm T p

noncomputable def witnessPsi : Fin 2 → ℂ :=
  ![(63 : ℂ) / 65, (16 : ℂ) / 65]

noncomputable def witnessV : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(4 : ℂ) / 5, (3 : ℂ) / 5;
     (-3 : ℂ) / 5, (4 : ℂ) / 5]

noncomputable def witnessZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), -1]

noncomputable def witnessJointPsi : (Fin 2 × (Fin 2 × Fin 2)) → ℂ :=
  fun x => ((witnessZ ^ x.2.1.val) *ᵥ witnessPsi) x.1 / 2

noncomputable def witnessRho :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
  Matrix.vecMulVec witnessJointPsi (star witnessJointPsi)

noncomputable def witnessBlock : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun c => witnessZ ^ c.2.val * witnessV * witnessZ ^ c.1.val

noncomputable def witnessU :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
  Matrix.blockDiagonal witnessBlock

noncomputable def witnessT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun x : Fin 2 × Fin 2 =>
    (!![(3024 : ℂ), 945; 576, -320] x.1 x.2) / 4225)

private theorem witnessRho_posSemidef : witnessRho.PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star witnessJointPsi

private theorem witnessRho_trace : witnessRho.trace = 1 := by
  rw [witnessRho, Matrix.trace_vecMulVec]
  norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    witnessJointPsi, witnessZ, witnessPsi, Matrix.mulVec, Matrix.diagonal, Pi.star_def]

private theorem witnessBlock_unitary (c : Fin 2 × Fin 2) :
    (witnessBlock c)ᴴ * witnessBlock c = 1 ∧
    witnessBlock c * (witnessBlock c)ᴴ = 1 := by
  rcases c with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;> constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessBlock, witnessZ, witnessV, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, map_ofNat]

private theorem witnessU_unitary :
    witnessUᴴ * witnessU = 1 ∧ witnessU * witnessUᴴ = 1 := by
  constructor
  · rw [witnessU, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun c => (witnessBlock c)ᴴ * witnessBlock c) =
        (1 : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :=
      funext fun c => (witnessBlock_unitary c).1
    rw [h, Matrix.blockDiagonal_one]
  · rw [witnessU, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    have h : (fun c => witnessBlock c * (witnessBlock c)ᴴ) =
        (1 : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ) :=
      funext fun c => (witnessBlock_unitary c).2
    rw [h, Matrix.blockDiagonal_one]

end D5.S3.Quantum.Information.SpacetimeDensitySchattenSubadditivityRefutation
