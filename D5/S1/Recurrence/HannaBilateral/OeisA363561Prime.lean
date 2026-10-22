/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363561Prime
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363561Prime
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at prime indices. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18664; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo
import D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo


set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363561Prime

open D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo (a)

/-- A363561 ("a(p) = p*2^((p-1)/2) + 2^p for primes p > 3 (conjecture)"). -/
def claim : Prop := ∀ p : ℕ, p.Prime → 3 < p → a p = p * 2 ^ ((p - 1) / 2) + 2 ^ p

end D5.S1.Recurrence.HannaBilateral.OeisA363561Prime

namespace D5.S1.Recurrence.HannaBilateral.OeisA363561Prime
theorem result : claim := by
  intro p hp h3
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA (Real.sqrt 2 : ℂ) p = _
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))
  have he : 2*((p-1)/2) = p-1 := Nat.mul_div_cancel' (hp.even_sub_one (by omega)).two_dvd
  have hsp : (Real.sqrt 2 : ℂ)^(p-1) = 2^((p-1)/2) := by
    rw [← he, pow_mul, hs]
    simp
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_prime _ p hp h3, hsp, pow_mul, hs]
end D5.S1.Recurrence.HannaBilateral.OeisA363561Prime
