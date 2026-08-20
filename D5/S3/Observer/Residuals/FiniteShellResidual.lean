/- GID: D5/S3/Observer/Residuals/FiniteShellResidual
   generality: G
   mirror-B: D5/B/S3/Observer/Residuals/FiniteShellResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite shell compression can vanish while its complementary defect remains nonzero. -/

import Mathlib

namespace D5.S3.Observer.Residuals.FiniteShellResidual

/- The finite listing predicate selects the first N coordinates of a shell with
   one additional residual coordinate. -/
def shellProjection (N : Nat) : Matrix (Fin (N + 1)) (Fin (N + 1)) Real :=
  Matrix.diagonal (fun i => if i.1 < N then 1 else 0)

def residualProjection (N : Nat) : Matrix (Fin (N + 1)) (Fin (N + 1)) Real :=
  Matrix.diagonal (fun i => if N ≤ i.1 then 1 else 0)

/- The defect is supplied by an independent predicate: only the last listed
   coordinate carries a unit defect weight. -/
def defectOperator (N : Nat) : Matrix (Fin (N + 1)) (Fin (N + 1)) Real :=
  Matrix.diagonal (fun i => if i.1 = N then 1 else 0)

theorem shell_compression_zero (N : Nat) :
    shellProjection N * defectOperator N * shellProjection N = 0 := by
  simp only [shellProjection, defectOperator]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.1 < N
    · have hne : i.1 ≠ N := by omega
      simp [hi, hne]
    · have hieq : i.1 = N := by omega
      simp [hieq]
  · simp [hij]

theorem residual_compression_nonzero (N : Nat) :
    residualProjection N * defectOperator N * residualProjection N ≠ 0 := by
  intro h
  have hentry := congrArg (fun M => M (Fin.last N) (Fin.last N)) h
  simp [residualProjection, defectOperator, Matrix.diagonal_mul_diagonal] at hentry

/-- A finite shell check records only its compressed defect and cannot by itself
    establish vanishing of the complementary residual block. -/
theorem finite_shell_check_does_not_close_residual :
    ∀ N : Nat,
      shellProjection N * defectOperator N * shellProjection N = 0 ∧
        residualProjection N * defectOperator N * residualProjection N ≠ 0 ∧
          ¬ (shellProjection N * defectOperator N * shellProjection N = 0 →
            residualProjection N * defectOperator N * residualProjection N = 0) := by
  intro N
  refine ⟨shell_compression_zero N, residual_compression_nonzero N, ?_⟩
  intro h
  exact residual_compression_nonzero N (h (shell_compression_zero N))

#print axioms finite_shell_check_does_not_close_residual

end D5.S3.Observer.Residuals.FiniteShellResidual
