/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at powers of two. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18663; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo


set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo

open D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo (coeffA)

/-- A363561: the coefficients for `c = sqrt(2)`. -/
noncomputable def a (m : ℕ) : ℂ := coeffA (Real.sqrt 2 : ℂ) m

/-- A363561 ("a(2^n) = 2^(2^n) for n > 0 (conjecture)"). -/
def claim : Prop := ∀ n : ℕ, 0 < n → a (2 ^ n) = 2 ^ (2 ^ n)

end D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo

namespace D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo
theorem result : claim := by
  intro n hn
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA (Real.sqrt 2 : ℂ) (2^n) = _
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two _ n hn, pow_succ', pow_mul, hs]
end D5.S1.Recurrence.HannaBilateral.OeisA363561PowerOfTwo
