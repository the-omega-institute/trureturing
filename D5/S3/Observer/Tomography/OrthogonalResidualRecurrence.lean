/- GID: D5/S3/Observer/Tomography/OrthogonalResidualRecurrence
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/OrthogonalResidualRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recursive orthogonal extraction splits each residual and the ambient Hilbert space. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-08-18):
   * Repository search found the nearby finite-stage expansion theorem, but no declaration with
     independently constructed accumulated and residual towers and all direct-sum clauses.
   * Pinned Mathlib and Loogle returned the exact declarations
     `ClosedSubmodule.inf_orthogonal` and
     `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`; both are applied below.
   * LeanSearch was reachable through its public page, but the available response contained no
     exact result for the closed-subspace residual recurrence query. -/

namespace D5.S3.Observer.Tomography.OrthogonalResidualRecurrence

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The accumulated closed subspace, constructed from an initial subspace and successive shells. -/
def accumulatedSubspace
    (M : ClosedSubmodule ℝ H) (E : ℕ → ClosedSubmodule ℝ H) :
    ℕ → ClosedSubmodule ℝ H
  | 0 => M
  | n + 1 => accumulatedSubspace M E n ⊔ E (n + 1)

/-- The residual tower, constructed independently by successive orthogonal intersections. -/
def recursiveResidual
    (M : ClosedSubmodule ℝ H) (E : ℕ → ClosedSubmodule ℝ H) :
    ℕ → ClosedSubmodule ℝ H
  | 0 => Mᗮ
  | n + 1 => recursiveResidual M E n ⊓ (E (n + 1))ᗮ

/-- Selecting every next shell inside the current recursively constructed residual identifies the
next residual with the accumulated space's orthogonal complement. It also gives orthogonal
direct-sum decompositions of the current residual and of the ambient Hilbert space. -/
theorem orthogonal_residual_recurrence
    (M : ClosedSubmodule ℝ H)
    (E : ℕ → ClosedSubmodule ℝ H)
    (hchoose : ∀ n,
      (E (n + 1)).toSubmodule ≤ (recursiveResidual M E n).toSubmodule)
    (n : ℕ) :
    recursiveResidual M E (n + 1) = (accumulatedSubspace M E (n + 1))ᗮ ∧
      (E (n + 1)).toSubmodule ⟂
        (recursiveResidual M E (n + 1)).toSubmodule ∧
      (recursiveResidual M E n).toSubmodule =
        (E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule ∧
      (accumulatedSubspace M E (n + 1)).toSubmodule ⟂
        (recursiveResidual M E (n + 1)).toSubmodule ∧
      (⊤ : Submodule ℝ H) =
        (accumulatedSubspace M E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule := by
  have hresidual : ∀ k,
      recursiveResidual M E k = (accumulatedSubspace M E k)ᗮ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [recursiveResidual, accumulatedSubspace]
        rw [ih]
        exact ClosedSubmodule.inf_orthogonal _ _
  have hsplitOrtho :
      (E (n + 1)).toSubmodule ⟂
        (recursiveResidual M E (n + 1)).toSubmodule := by
    apply (Submodule.isOrtho_orthogonal_right (E (n + 1)).toSubmodule).mono_right
    change (recursiveResidual M E n ⊓ (E (n + 1))ᗮ).toSubmodule ≤
      (E (n + 1)).toSubmoduleᗮ
    exact inf_le_right
  have hsplit :=
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hchoose n)
  have hsplitEq :
      (recursiveResidual M E n).toSubmodule =
        (E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule := by
    calc
      (recursiveResidual M E n).toSubmodule =
          (E (n + 1)).toSubmodule ⊔
            (E (n + 1)).toSubmoduleᗮ ⊓
              (recursiveResidual M E n).toSubmodule := hsplit.symm
      _ = (E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E n).toSubmodule ⊓
            (E (n + 1)).toSubmoduleᗮ := by rw [inf_comm]
      _ = (E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule := by
        rfl
  have hambientOrtho :
      (accumulatedSubspace M E (n + 1)).toSubmodule ⟂
        (recursiveResidual M E (n + 1)).toSubmodule := by
    rw [hresidual (n + 1)]
    exact Submodule.isOrtho_orthogonal_right _
  have hambientEq :
      (⊤ : Submodule ℝ H) =
        (accumulatedSubspace M E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule := by
    rw [hresidual (n + 1)]
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection.symm
  exact ⟨hresidual (n + 1), hsplitOrtho, hsplitEq, hambientOrtho, hambientEq⟩

/-- The shell-selection hypothesis and conclusion are jointly inhabited in a real Hilbert space. -/
example (n : ℕ) :
    let M : ClosedSubmodule ℝ ℝ := ⊥
    let E : ℕ → ClosedSubmodule ℝ ℝ := fun _ => ⊥
    recursiveResidual M E (n + 1) = (accumulatedSubspace M E (n + 1))ᗮ ∧
      (E (n + 1)).toSubmodule ⟂ (recursiveResidual M E (n + 1)).toSubmodule ∧
      (recursiveResidual M E n).toSubmodule =
        (E (n + 1)).toSubmodule ⊔ (recursiveResidual M E (n + 1)).toSubmodule ∧
      (accumulatedSubspace M E (n + 1)).toSubmodule ⟂
        (recursiveResidual M E (n + 1)).toSubmodule ∧
      (⊤ : Submodule ℝ ℝ) =
        (accumulatedSubspace M E (n + 1)).toSubmodule ⊔
          (recursiveResidual M E (n + 1)).toSubmodule := by
  dsimp
  apply orthogonal_residual_recurrence
  intro k
  exact bot_le

#print axioms orthogonal_residual_recurrence

end

end D5.S3.Observer.Tomography.OrthogonalResidualRecurrence
