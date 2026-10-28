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
import D5.S3.Quantum.PureState.PureStateHandshake

set_option linter.style.longLine false

open scoped BigOperators Matrix Kronecker ComplexOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.FiniteDimensional D5.S3.Quantum.PureState

namespace D5.S3.Quantum.Information.SpacetimeDensitySchattenSubadditivityRefutation

/- Milekhin, Adamska and Preskill, arXiv:2502.12240v2, Conjecture 1.
   The correlation antecedent is Eq. (9), with the ordering specified by Eq. (4).
   The Schatten norm is the quantity defined in footnote a. -/

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

noncomputable def witnessJointPsi : (Fin 2 × (Fin 2 × Fin 2)) → ℂ :=
  fun x => ((qubitZ ^ x.2.1.val) *ᵥ witnessPsi) x.1 / 2

noncomputable def witnessRho :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
  PureStateHandshake.rankOneDensity witnessJointPsi

noncomputable def witnessBlock : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ :=
  fun c => qubitZ ^ c.2.val * witnessV * qubitZ ^ c.1.val

noncomputable def witnessU :
    Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ :=
  Matrix.blockDiagonal witnessBlock

noncomputable def witnessT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun x : Fin 2 × Fin 2 =>
    (!![(3024 : ℂ), 945; 576, -320] x.1 x.2) / 4225)

private theorem witnessRho_posSemidef : witnessRho.PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star witnessJointPsi

private theorem witnessRho_trace : witnessRho.trace = 1 := by
  rw [witnessRho, PureStateHandshake.rankOneDensity, Matrix.trace_vecMulVec]
  norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
    witnessJointPsi.eq_1, qubitZ, witnessPsi.eq_1, Matrix.mulVec, Matrix.diagonal, Pi.star_def]

private theorem witnessBlock_unitary (c : Fin 2 × Fin 2) :
    (witnessBlock c)ᴴ * witnessBlock c = 1 ∧
    witnessBlock c * (witnessBlock c)ᴴ = 1 := by
  rcases c with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;> constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [witnessBlock.eq_1, qubitZ, witnessV.eq_1, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.vecHead,
      Matrix.vecTail, map_ofNat]

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

/- The observable product preserves each control sector before any entry expansion. -/
private theorem witness_eq9
    (OA : Matrix (Fin 2) (Fin 2) ℂ) (OB : Matrix (Fin 2) (Fin 2) ℂ) :
    (witnessT * (OA ⊗ₖ OB)).trace =
      (witnessRho * (OA ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) *
        witnessUᴴ * (OB ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) *
        witnessU).trace := by
  have compress :
      (OA ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) * witnessUᴴ *
          (OB ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) * witnessU =
        Matrix.blockDiagonal (fun c => OA * (witnessBlock c)ᴴ * OB * witnessBlock c) := by
    simp only [witnessU, Matrix.kronecker_one, Matrix.blockDiagonal_conjTranspose,
      ← Matrix.blockDiagonal_mul]
  have rankOne (M :
      Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ) :
      (witnessRho * M).trace = star witnessJointPsi ⬝ᵥ (M *ᵥ witnessJointPsi) := by
    rw [Matrix.trace_mul_comm]
    exact D5.S3.Quantum.QuantumChannels.TwoPositiveTransitionTrace.trace_rank_one M
      witnessJointPsi
  have blockAction
      (F : (Fin 2 × Fin 2) → Matrix (Fin 2) (Fin 2) ℂ)
      (x : (Fin 2 × (Fin 2 × Fin 2)) → ℂ) (q : Fin 2) (c : Fin 2 × Fin 2) :
      (Matrix.blockDiagonal F *ᵥ x) (q, c) = ∑ j : Fin 2, F c q j * x (j, c) := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply,
      ite_mul]
  have regroup :
      witnessRho * (OA ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) *
          witnessUᴴ * (OB ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) * witnessU =
        witnessRho * ((OA ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) *
          witnessUᴴ * (OB ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) * witnessU) := by
    simp only [Matrix.mul_assoc]
  rw [regroup, compress, rankOne]
  simp only [dotProduct, Fintype.sum_prod_type, blockAction, Pi.star_apply]
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type,
    Fin.sum_univ_two, witnessT, witnessJointPsi.eq_1, witnessBlock.eq_1, qubitZ, witnessV.eq_1,
    witnessPsi.eq_1, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Matrix.diagonal, map_ofNat]
  ring

private theorem witness_partialLeft :
    partialTraceLeft witnessT = Matrix.diagonal ![(144 : ℂ) / 169, (25 : ℂ) / 169] := by
  let r : Fin 2 × Fin 2 → ℝ :=
    fun x => (!![(3024 : ℝ), 945; 576, -320] x.1 x.2) / 4225
  have hT : witnessT = Matrix.diagonal (fun x => (r x : ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [witnessT, r, Matrix.diagonal]
  rw [hT, D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.partialTraceLeft_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, Fin.sum_univ_two, Matrix.diagonal]

private theorem witness_partialRight :
    partialTraceRight witnessT = Matrix.diagonal ![(3969 : ℂ) / 4225, (256 : ℂ) / 4225] := by
  let r : Fin 2 × Fin 2 → ℝ :=
    fun x => (!![(3024 : ℝ), 945; 576, -320] x.1 x.2) / 4225
  have hT : witnessT = Matrix.diagonal (fun x => (r x : ℂ)) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [witnessT, r, Matrix.diagonal]
  rw [hT, D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation.partialTraceRight_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [r, Fin.sum_univ_two, Matrix.diagonal]

private theorem witness_norm_values :
    schattenNorm witnessT 2 = Real.sqrt ((10471777 : ℝ) / 17850625) ∧
    schattenNorm (partialTraceLeft witnessT) 2 = Real.sqrt ((21361 : ℝ) / 28561) ∧
    schattenNorm (partialTraceRight witnessT) 2 = Real.sqrt ((15818497 : ℝ) / 17850625) := by
  have normTwo {d : Type} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
      schattenNorm A 2 = Real.sqrt (RCLike.re (Aᴴ * A).trace) := by
    have h : (Aᴴ * (Aᴴ)ᴴ).IsHermitian :=
      Matrix.isHermitian_mul_conjTranspose_self Aᴴ
    have hc : h.cfc (fun x : ℝ => x) = Aᴴ * (Aᴴ)ᴴ :=
      (h.cfc_eq (fun x : ℝ => x)).symm.trans (cfc_id' ℝ _ h.isSelfAdjoint)
    unfold schattenNorm
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    rw [hc, Matrix.conjTranspose_conjTranspose, Real.sqrt_eq_rpow]
  rw [witness_partialLeft, witness_partialRight]
  constructor
  · rw [normTwo, witnessT, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, Pi.star_apply, map_ofNat,
      RCLike.re_eq_complex_re]
  · constructor <;> rw [normTwo, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] <;>
      norm_num [Fin.sum_univ_two, Pi.star_apply, map_ofNat, RCLike.re_eq_complex_re]

private theorem witness_violation :
    1 + schattenNorm witnessT 2 <
      schattenNorm (partialTraceLeft witnessT) 2 + schattenNorm (partialTraceRight witnessT) 2 := by
  obtain ⟨hT, hL, hR⟩ := witness_norm_values
  rw [hT, hL, hR]
  have upper : Real.sqrt ((10471777 : ℝ) / 17850625) ≤ (77 : ℝ) / 100 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have lowerLeft : (43 : ℝ) / 50 ≤ Real.sqrt ((21361 : ℝ) / 28561) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have lowerRight : (47 : ℝ) / 50 ≤ Real.sqrt ((15818497 : ℝ) / 17850625) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  calc
    1 + Real.sqrt ((10471777 : ℝ) / 17850625) ≤ 1 + 77 / 100 := add_le_add (le_refl 1) upper
    _ < 43 / 50 + 47 / 50 := by norm_num
    _ ≤ _ := add_le_add lowerLeft lowerRight

/-- The three-qubit rational state violates Conjecture 1 at exponent two. -/
theorem result : ¬ claim := by
  intro h
  have hu := witnessU_unitary
  have hle := h (Fin 2) (Fin 2 × Fin 2) (Fin 2) (Fin 2 × Fin 2)
    witnessRho witnessU witnessT (2 : ℝ) witnessRho_posSemidef witnessRho_trace
    hu.1 hu.2 witness_eq9 (by norm_num)
  exact (not_le_of_gt witness_violation) hle

end D5.S3.Quantum.Information.SpacetimeDensitySchattenSubadditivityRefutation
