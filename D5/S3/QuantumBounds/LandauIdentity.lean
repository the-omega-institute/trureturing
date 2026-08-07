/- GID: D5/S3/QuantumBounds/LandauIdentity
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/LandauIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the algebraic Landau identity for finite complex matrix observables. -/

/- Library-search audit trail (2026-08-07):
   * Local mathlib grep terms: `Landau`, `CHSH`, `Tsirelson`,
     `commutator.*kronecker`, `kronecker.*commutator`, `mul_kronecker_mul`, and
     `one_kronecker_one`. No theorem with the target noncommutative Landau identity was found.
   * `Mathlib.Algebra.Star.CHSH.CHSH_id` was found, but it assumes a commutative ring and proves
     a different idempotence identity, so it cannot discharge the matrix statement here.
   * Reusable Kronecker algebra was found in `Mathlib.LinearAlgebra.Matrix.Kronecker`:
     `Matrix.mul_kronecker_mul`, `Matrix.one_kronecker_one`, `Matrix.kronecker_apply`,
     `Matrix.add_kronecker`, and `Matrix.kronecker_add`. There is no subtraction-specialized
     Kronecker lemma. The proof delegates tensor multiplication and identities to the upstream
     lemmas, verifies the one difference expansion entrywise, and only then normalizes additively.
   * The pinned worktree has no executable local `loogle` client (`lake env loogle` could not
     launch it), so no online or remote search result is claimed.
-/

import Mathlib

namespace D5.S3.QuantumBounds.LandauIdentity

open scoped Kronecker

/-- The square of the CHSH operator is four times the identity plus the negative tensor product
of the two local commutators. Hermiticity records the observable context; the algebraic identity
itself uses the four involution hypotheses. -/
theorem landau_identity {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A₀ A₁ : Matrix m m ℂ) (B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian ∧ A₀ ^ 2 = 1)
    (hA₁ : A₁.IsHermitian ∧ A₁ ^ 2 = 1)
    (hB₀ : B₀.IsHermitian ∧ B₀ ^ 2 = 1)
    (hB₁ : B₁.IsHermitian ∧ B₁ ^ 2 = 1) :
    let S := A₀ ⊗ₖ B₀ + A₀ ⊗ₖ B₁ + A₁ ⊗ₖ B₀ - A₁ ⊗ₖ B₁
    let C := -((A₀ * A₁ - A₁ * A₀) ⊗ₖ (B₀ * B₁ - B₁ * B₀))
    S ^ 2 = 4 • (1 : Matrix (m × n) (m × n) ℂ) + C := by
  rcases hA₀ with ⟨_, hA₀Square⟩
  rcases hA₁ with ⟨_, hA₁Square⟩
  rcases hB₀ with ⟨_, hB₀Square⟩
  rcases hB₁ with ⟨_, hB₁Square⟩
  dsimp
  have hCommutatorTensor :
      (A₀ * A₁ - A₁ * A₀) ⊗ₖ (B₀ * B₁ - B₁ * B₀) =
        (A₀ * A₁) ⊗ₖ (B₀ * B₁) - (A₀ * A₁) ⊗ₖ (B₁ * B₀) -
          (A₁ * A₀) ⊗ₖ (B₀ * B₁) + (A₁ * A₀) ⊗ₖ (B₁ * B₀) := by
    ext i j
    simp
    ring
  rw [hCommutatorTensor]
  simp only [pow_two, sub_mul, mul_sub, add_mul, mul_add]
  simp only [← Matrix.mul_kronecker_mul]
  simp only [← pow_two, hA₀Square, hA₁Square, hB₀Square, hB₁Square,
    Matrix.one_kronecker_one]
  abel

end D5.S3.QuantumBounds.LandauIdentity
