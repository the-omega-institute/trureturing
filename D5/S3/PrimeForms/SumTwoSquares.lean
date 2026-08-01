/- GID: D5/S3/PrimeForms/SumTwoSquares
   generality: G
   mirror-B: D5/B/S3/PrimeForms/SumTwoSquares
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A prime congruent to one modulo four is a sum of two natural squares. -/

import Mathlib.NumberTheory.SumTwoSquares

namespace D5.S3.PrimeForms.SumTwoSquares

/-- A prime congruent to one modulo four is a sum of two natural squares. -/
theorem prime_eq_sq_add_sq_of_mod_four_eq_one (p : ℕ) (hp : p.Prime)
    (hmod : p % 4 = 1) : ∃ a b : ℕ, p = a ^ 2 + b ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by simp [hmod])
  exact ⟨a, b, hab.symm⟩

end D5.S3.PrimeForms.SumTwoSquares
