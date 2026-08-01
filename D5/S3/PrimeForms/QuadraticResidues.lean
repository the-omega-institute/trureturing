/- GID: D5/S3/PrimeForms/QuadraticResidues
   generality: G
   mirror-B: D5/B/S3/PrimeForms/QuadraticResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Squares are zero or one modulo four, so two squares never sum to three modulo four. -/

import Mathlib

namespace D5.S3.PrimeForms.QuadraticResidues

theorem square_residues_and_sum_obstruction :
    (∀ n : ℕ, n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1) ∧
      (∀ a b : ℕ, (a ^ 2 + b ^ 2) % 4 ≠ 3) := by
  have hsq : ∀ n : ℕ, n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
    intro n
    have hn_decomp : n = n % 2 + 2 * (n / 2) := by omega
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · left
      rw [hn_decomp, hn]
      ring_nf
      omega
    · right
      rw [hn_decomp, hn]
      ring_nf
      omega
  refine ⟨hsq, ?_⟩
  intro a b
  rcases hsq a with ha | ha <;> rcases hsq b with hb | hb <;> omega

end D5.S3.PrimeForms.QuadraticResidues
