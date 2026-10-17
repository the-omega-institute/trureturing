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

end D5.S3.Quantum.Entanglement.FixedMarginalNegativityRefutation
