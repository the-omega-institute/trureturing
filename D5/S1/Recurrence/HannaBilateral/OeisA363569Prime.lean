/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363569Prime
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363569Prime
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at prime indices. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18666; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
import D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363569Prime

open D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo (a)

/-- A363569 ("a(p) = p*(-1)^((p-1)/2) - 1 for primes p > 3 (conjecture)"). -/
def claim : Prop := ∀ p : ℕ, p.Prime → 3 < p → a p = p * (-1) ^ ((p - 1) / 2) - 1

end D5.S1.Recurrence.HannaBilateral.OeisA363569Prime

namespace D5.S1.Recurrence.HannaBilateral.OeisA363569Prime
theorem result : claim := by
  intro p hp h3
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA Complex.I p = _
  have he : 2*((p-1)/2) = p-1 := Nat.mul_div_cancel' (hp.even_sub_one (by omega)).two_dvd
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have hip : Complex.I^(p-1) = (-1:ℂ)^((p-1)/2) := by
    rw [← he, pow_mul, Complex.I_sq]
    simp
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime _ p hp h3, hip, pow_mul, Complex.I_sq, ho.neg_one_pow]
  ring
end D5.S1.Recurrence.HannaBilateral.OeisA363569Prime
