/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at powers of two. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18665; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo

open D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo (coeffA)

/-- A363569: the coefficients for `c = i`, `i^2 = -1`. -/
noncomputable def a (m : ℕ) : ℂ := coeffA Complex.I m

/-- A363569 ("a(2^n) = 1 for n > 0 (conjecture)"). -/
def claim : Prop := ∀ n : ℕ, 0 < n → a (2 ^ n) = 1

end D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo

namespace D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo
theorem result : claim := by
  intro n hn
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA Complex.I (2^n) = _
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two _ n hn, pow_succ', pow_mul, Complex.I_sq]
  exact (Even.pow_of_ne_zero (even_two : Even (2:ℕ)) (Nat.ne_of_gt hn)).neg_one_pow
end D5.S1.Recurrence.HannaBilateral.OeisA363569PowerOfTwo
