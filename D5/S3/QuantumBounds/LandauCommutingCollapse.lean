/- GID: D5/S3/QuantumBounds/LandauCommutingCollapse
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/LandauCommutingCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Collapse the CHSH square when either local observable pair commutes. -/

import D5.S3.QuantumBounds.LandauIdentity

/-!
# CHSH square under local commutativity

For finite complex Hermitian involutions, this module proves that the CHSH operator has square
`4I` whenever Alice's local pair or Bob's local pair commutes. This is the algebraic square
identity under a commuting local pair.

It does not state an expectation bound of `2` or an operator-norm CHSH bound of `2`, and it
introduces no state or optimization problem.
-/

namespace D5.S3.QuantumBounds.LandauCommutingCollapse

open scoped Kronecker

theorem chsh_square_eq_four_of_local_pair_commutes {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A₀ A₁ : Matrix m m ℂ) (B₀ B₁ : Matrix n n ℂ)
    (hA₀ : A₀.IsHermitian ∧ A₀ ^ 2 = 1)
    (hA₁ : A₁.IsHermitian ∧ A₁ ^ 2 = 1)
    (hB₀ : B₀.IsHermitian ∧ B₀ ^ 2 = 1)
    (hB₁ : B₁.IsHermitian ∧ B₁ ^ 2 = 1)
    (hLocal : A₀ * A₁ = A₁ * A₀ ∨ B₀ * B₁ = B₁ * B₀) :
    let S := A₀ ⊗ₖ B₀ + A₀ ⊗ₖ B₁ + A₁ ⊗ₖ B₀ - A₁ ⊗ₖ B₁
    S ^ 2 = 4 • (1 : Matrix (m × n) (m × n) ℂ) := by
  dsimp
  rw [LandauIdentity.landau_identity A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁]
  rcases hLocal with hA | hB
  · rw [hA]
    simp
  · rw [hB]
    simp

end D5.S3.QuantumBounds.LandauCommutingCollapse
