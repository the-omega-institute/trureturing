/- GID: D5/S3/PrimeForms/SumTwoSquaresClassification
   generality: G
   mirror-B: D5/B/S3/PrimeForms/SumTwoSquaresClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A natural number is a sum of two squares iff primes three mod four occur evenly. -/

import Mathlib.NumberTheory.SumTwoSquares

/- Provenance: thin honest wrapper over pinned mathlib's two-squares
   classification (`Nat.eq_sq_add_sq_iff`, stated over `n.primeFactors` with
   `padicValNat`); the wrapper glues that form to the all-primes
   `Nat.factorization` form, using that primes outside the support carry
   exponent zero (`Nat.factorization_eq_zero_of_not_dvd`, `factorization_zero`). -/

namespace D5.S3.PrimeForms.SumTwoSquaresClassification

/--
Two-axis norm classification: a natural number `n` is a sum of two natural
squares if and only if every prime `q` with `q % 4 = 3` occurs to an even
exponent in the factorization of `n`.  Primes not dividing `n` (and the case
`n = 0`) carry exponent zero, which is even, so the all-primes quantifier
agrees with mathlib's restriction to `n.primeFactors`.
-/
theorem eq_sq_add_sq_iff_even_factorization (n : ℕ) :
    (∃ a b : ℕ, n = a ^ 2 + b ^ 2) ↔
      ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (n.factorization q) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro H q hq hq4
    by_cases hmem : q ∈ n.primeFactors
    · rw [Nat.factorization_def n hq]
      exact H q hmem hq4
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnd : ¬q ∣ n := fun hdvd =>
          hmem (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hn.ne'⟩)
        rw [Nat.factorization_eq_zero_of_not_dvd hnd]
        exact ⟨0, rfl⟩
  · intro H q hqmem hq4
    have hq := Nat.prime_of_mem_primeFactors hqmem
    have heven := H q hq hq4
    rwa [Nat.factorization_def n hq] at heven

end D5.S3.PrimeForms.SumTwoSquaresClassification
