/- GID: D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim; result=D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.result; claim=D5/S3/Quantum/Entanglement/FixedMarginalNegativityRefutation.claim
   digest: Fixed two-qutrit marginals admit greater negativity than the Baio et al. candidate. -/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.FixedMarginalNegativityRefutation

open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
  (partialTransposeB IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceLeft partialTraceRight partialTraceLeft_kronecker partialTraceRight_kronecker)

/-- The negativity of Eq. (4), with partial transposition on the second factor. -/
noncomputable def negativity (R : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : ℝ :=
  (traceNorm (partialTransposeB R) - 1) / 2

/-- The first fixed marginal in Eq. (24). -/
noncomputable def marginalA (l₁ l₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![((1 - l₁ - l₂ : ℝ) : ℂ), (l₁ : ℂ), (l₂ : ℂ)]

/-- The second fixed marginal in Eq. (24). -/
noncomputable def marginalB (m₁ m₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![((1 - m₁ - m₂ : ℝ) : ℂ), (m₁ : ℂ), (m₂ : ℂ)]

/-- The candidate of Eq. (27), written in the matrix form of Eq. (30). -/
noncomputable def candidate (l₁ l₂ m₁ m₂ : ℝ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let φ : Fin 3 × Fin 3 → ℂ := Function.uncurry
    ![![(Real.sqrt (1 - l₁ - l₂) : ℂ), 0, 0],
      ![0, (Real.sqrt m₁ : ℂ), 0], ![0, 0, (Real.sqrt m₂ : ℂ)]]
  vecMulVec φ (star φ) + diagonal (Function.uncurry
    ![![0, 0, 0], ![((l₁ - m₁ : ℝ) : ℂ), 0, 0], ![((l₂ - m₂ : ℝ) : ℂ), 0, 0]])

/-- The fixed-marginal maximizing conjecture of Section IV, restricted to Eq. (27). -/
def claim : Prop :=
  ∀ (l₁ l₂ m₁ m₂ : ℝ),
    l₂ ≤ l₁ → l₁ ≤ 1 - l₁ - l₂ → 0 ≤ l₂ →
    m₂ ≤ m₁ → m₁ ≤ 1 - m₁ - m₂ → 0 ≤ m₂ →
    m₁ + m₂ ≤ l₁ + l₂ → m₁ < l₁ → m₂ < l₂ →
    ∀ R : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ,
      IsDensity R → partialTraceRight R = marginalA l₁ l₂ →
      partialTraceLeft R = marginalB m₁ m₂ →
      negativity R ≤ negativity (candidate l₁ l₂ m₁ m₂)

private noncomputable def chi : Fin 3 × Fin 3 → ℂ :=
  Function.uncurry ![![7/10, 0, 0], ![0, 0, 1/10], ![0, 1/5, 0]]

private noncomputable def rho0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  vecMulVec chi (star chi) + diagonal
    (Function.uncurry ![![0, 0, 0], ![45/100, 1/100, 0], ![0, 0, 0]])

private noncomputable def rho : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (99/100 : ℂ) • rho0 + (1/100 : ℂ) •
    (marginalA (47/100) (4/100) ⊗ₖ marginalB (5/100) (1/100))

private theorem rho_density : IsDensity rho := by
  constructor
  · apply PosSemidef.add
    · apply PosSemidef.smul (a := (99/100 : ℂ))
      · apply (posSemidef_vecMulVec_self_star chi).add
        apply PosSemidef.diagonal
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> norm_num [Complex.le_def, Matrix.cons_val_two]
      · norm_num [Complex.le_def, Matrix.cons_val_two]
    · apply PosSemidef.smul (a := (1/100 : ℂ))
      · rw [marginalA.eq_1, marginalB.eq_1, diagonal_kronecker_diagonal]
        apply PosSemidef.diagonal
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> norm_num [Complex.le_def, Matrix.cons_val_two]
      · norm_num [Complex.le_def, Matrix.cons_val_two]
  · norm_num [rho.eq_1, rho0.eq_1, chi.eq_1, marginalA.eq_1, marginalB.eq_1,
      Matrix.trace, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem rho_marginalA : partialTraceRight rho = marginalA (47/100) (4/100) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, rho.eq_1, rho0.eq_1, chi.eq_1,
      marginalA.eq_1, marginalB.eq_1, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem rho_marginalB : partialTraceLeft rho = marginalB (5/100) (1/100) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft, rho.eq_1, rho0.eq_1, chi.eq_1,
      marginalA.eq_1, marginalB.eq_1, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]


private noncomputable def rhoPT : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  fun p q =>
    if p = q then (Function.uncurry
      ![![244853/500000, 49/200000, 49/1000000],
        ![224959/500000, 2027/200000, 9947/1000000],
        ![47/125000, 1981/50000, 1/250000]]) p
    else if (p = (0, 1) ∧ q = (2, 0)) ∨ (p = (2, 0) ∧ q = (0, 1)) then 693/5000
    else if (p = (0, 2) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 2)) then 693/10000
    else if (p = (1, 1) ∧ q = (2, 2)) ∨ (p = (2, 2) ∧ q = (1, 1)) then 99/5000
    else 0

private theorem rho_pt_eq : partialTransposeB rho = rhoPT := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
      Fin.reduceFinMk, partialTransposeB, rho.eq_1, rho0.eq_1, chi.eq_1, rhoPT.eq_1,
      marginalA.eq_1, marginalB.eq_1, Matrix.vecMulVec_apply, Matrix.kronecker_apply,
      Matrix.cons_val_two, map_ofNat]

private noncomputable def K : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let a : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 1, 0], ![0, 0, 0], ![-1, 0, 0]]
  let b : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 7], ![-1, 0, 0], ![0, 0, 0]]
  let c : Fin 3 × Fin 3 → ℂ :=
    Function.uncurry ![![0, 0, 0], ![0, 1, 0], ![0, 0, -1]]
  (1/2 : ℂ) • vecMulVec a (star a) + (1/50 : ℂ) • vecMulVec b (star b) +
    (1/2 : ℂ) • vecMulVec c (star c)

private theorem K_hermitian : K.IsHermitian := by
  exact (((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])).add
    ((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def])) |>.add
    ((posSemidef_vecMulVec_self_star _).smul (by norm_num [Complex.le_def]))).isHermitian

set_option maxHeartbeats 1000000 in
-- The certificate checks all 81 entries of the rational projector product.
private theorem K_idempotent : K * K = K := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [K.eq_1, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two, map_ofNat]

private theorem reflection_unitary : (1 - (2 : ℂ) • K) ∈ unitaryGroup (Fin 3 × Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_sub, conjTranspose_one,
    conjTranspose_smul, K_hermitian.eq]
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, K_idempotent, star_ofNat, smul_smul]
  module

private theorem reflection_trace :
    ((1 - (2 : ℂ) • K) * partialTransposeB rho).trace =
      1 + 2 * (8168881/50000000 : ℂ) := by
  rw [rho_pt_eq]
  norm_num (config := { decide := true }) [-Fin.val_eq_zero_iff, Fin.reduceEq,
    Fin.reduceFinMk, K.eq_1, rhoPT.eq_1, Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_three, Matrix.cons_val_two,
    map_ofNat]

private theorem rho_negativity_lower : (8168881/50000000 : ℝ) ≤ negativity rho := by
  have h := (traceNorm_eq_max_re_tr_U (partialTransposeB rho)).2
    ⟨⟨1 - (2 : ℂ) • K, reflection_unitary⟩, rfl⟩
  rw [reflection_trace] at h
  norm_num at h
  rw [negativity.eq_1]
  linarith

end D5.S3.Quantum.Entanglement.FixedMarginalNegativityRefutation
