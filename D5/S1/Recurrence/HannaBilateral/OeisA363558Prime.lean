/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363558Prime
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363558Prime
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at prime indices. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18660; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363558Prime

open D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo (a)

/-- A363558 ("a(p) = p*2^(p-1) + 4^p for primes p > 3 (conjecture)"). -/
def claim : Prop := ∀ p : ℕ, p.Prime → 3 < p → a p = p * 2 ^ (p - 1) + 4 ^ p

end D5.S1.Recurrence.HannaBilateral.OeisA363558Prime

namespace D5.S1.Recurrence.HannaBilateral.OeisA363558Prime
theorem result : claim := by
  intro p hp h3
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA 2 p = _
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime 2 p hp h3]
  rw [pow_mul]
  norm_num
end D5.S1.Recurrence.HannaBilateral.OeisA363558Prime
