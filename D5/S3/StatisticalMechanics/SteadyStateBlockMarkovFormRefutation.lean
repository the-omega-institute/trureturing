/- GID: D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim; result=D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result; claim=D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.claim
   digest: An irreducible steady-state block of a four-state generator has no Markov form. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.SteadyStateBlockMarkovFormRefutation

open scoped BigOperators Matrix
open Matrix
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)

noncomputable section

/-- Real continuous-time generators use nonnegative off-diagonal rates and zero column sums. -/
def IsMarkovGenerator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, i ≠ j → 0 ≤ M i j) ∧ ∀ j, ∑ i, M i j = 0

/-- Every irreducible symmetry block containing a stationary probability has a Markov form. -/
def claim : Prop :=
  ∀ (N : ℕ) (L U : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → ℝ),
    IsMarkovGenerator L → U ∈ Matrix.orthogonalGroup (Fin N) ℝ → U * L = L * U →
    Probability p → L *ᵥ p = 0 →
    ∀ (d : ℕ) (V : Matrix (Fin N) (Fin d) ℝ) (u : ℝ),
      Vᵀ * V = 1 → L * V = V * (Vᵀ * L * V) → U * V = u • V →
      (∀ x, U *ᵥ x = u • x → ∃ c, V *ᵥ c = x) →
      (∃ c, V *ᵥ c = p) →
      (∀ X : Matrix (Fin d) (Fin d) ℂ,
        X ∈ Matrix.unitaryGroup (Fin d) ℂ →
        X * (Vᵀ * L * V).map Complex.ofReal = (Vᵀ * L * V).map Complex.ofReal * X →
        ∃ μ : ℂ, X = μ • (1 : Matrix (Fin d) (Fin d) ℂ)) →
      ∃ (S : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d) (Fin d) ℝ),
        IsUnit S ∧ IsMarkovGenerator B ∧
        S⁻¹ * (Vᵀ * L * V).map Complex.ofReal * S = B.map Complex.ofReal

private def L : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-295/256, 25/256, 25/256, 281/256;
     273/256, -303/256, 17/256, 17/256;
     7/256, 263/256, -313/256, 7/256;
     15/256, 15/256, 271/256, -305/256]

private def p : Fin 4 → ℝ := ![17/64, 17/64, 15/64, 15/64]

private def U : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/2, 1/2, -1/2, 1/2; 1/2, 1/2, 1/2, -1/2;
     -1/2, 1/2, 1/2, 1/2; 1/2, -1/2, 1/2, 1/2]

private def V : Matrix (Fin 4) (Fin 3) ℝ :=
  !![1/2, 1/2, -1/2; 1/2, 1/2, 1/2; 1/2, -1/2, 1/2; 1/2, -1/2, -1/2]

private def A : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 0; 5/64, -5/4, -1; -1/16, 1, -5/4]

private theorem generator : IsMarkovGenerator L := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | norm_num [L]
  · intro j
    fin_cases j <;> norm_num [L, Fin.sum_univ_succ]

private theorem orthogonal : U ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin 4) ℝ).mpr
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem symmetry : U * L = L * U := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, L, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem probability : Probability p := by
  constructor
  · intro i
    fin_cases i <;> norm_num [p]
  · norm_num [p, Fin.sum_univ_succ]

private theorem stationary : L *ᵥ p = 0 := by
  ext i
  fin_cases i <;> norm_num [L, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem frame : Vᵀ * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [V, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem restriction : Vᵀ * L * V = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [V, L, A, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem invariant : L * V = V * A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [L, V, A, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem eigenframe : U * V = V := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, V, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem contains_stationary : ∃ c, V *ᵥ c = p := by
  refine ⟨![1/2, 1/32, 0], ?_⟩
  ext i
  fin_cases i <;> norm_num [V, p, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem projector : V * Vᵀ = (1/2 : ℝ) • (1 + U) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [U, V, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem eigenspace (x : Fin 4 → ℝ) (hx : U *ᵥ x = (1 : ℝ) • x) :
    ∃ c, V *ᵥ c = x := by
  refine ⟨Vᵀ *ᵥ x, ?_⟩
  rw [Matrix.mulVec_mulVec, projector, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, hx, one_smul, ← two_smul ℝ x, smul_smul]
  norm_num

/-- The steady-state block conjecture fails even with real orthogonal symmetry. -/
theorem result : ¬ claim := by
  sorry

end
end D5.S3.StatisticalMechanics.SteadyStateBlockMarkovFormRefutation
