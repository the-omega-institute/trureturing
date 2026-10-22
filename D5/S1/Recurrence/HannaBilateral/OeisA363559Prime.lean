/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363559Prime
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363559Prime
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at prime indices. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18662; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
import D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363559Prime

open D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo (a)

/-- A363559 ("a(p) = p*3^(p-1) + 9^p for primes p > 3 (conjecture)"). -/
def claim : Prop := ∀ p : ℕ, p.Prime → 3 < p → a p = p * 3 ^ (p - 1) + 9 ^ p

end D5.S1.Recurrence.HannaBilateral.OeisA363559Prime

namespace D5.S1.Recurrence.HannaBilateral.OeisA363559Prime
theorem result : claim := by
  intro p hp h3
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA 3 p = _
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime 3 p hp h3, pow_mul]
  norm_num
end D5.S1.Recurrence.HannaBilateral.OeisA363559Prime
