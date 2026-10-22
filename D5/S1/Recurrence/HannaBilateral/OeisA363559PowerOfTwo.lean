/- GID: D5/S1/Recurrence/HannaBilateral/OeisA363559PowerOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/HannaBilateral/OeisA363559PowerOfTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hanna bilateral coefficients at powers of two. -/

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19885
admission_basis: open-problem-resolution (#18661; Proved)
escape_witness: none
Direct frozen dependencies: none.
utility: none; all results are universal identities, with no finite enumeration.
result: proof_shape: bind-only; escape_witness: none; settling result.
-/

import D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo

set_option autoImplicit false

namespace D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo

open D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo (coeffA)

/-- A363559: the coefficients for `c = 3`. -/
noncomputable def a (m : ℕ) : ℂ := coeffA 3 m

/-- A363559 ("a(2^n) = 9^(2^n) for n > 0 (conjecture)"). -/
def claim : Prop := ∀ n : ℕ, 0 < n → a (2 ^ n) = 9 ^ (2 ^ n)

end D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo

namespace D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo
theorem result : claim := by
  intro n hn
  change D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA 3 (2^n) = _
  rw [D5.S1.Recurrence.HannaBilateral.OeisA363558PowerOfTwo.coeffA_pow_two 3 n hn, pow_succ', pow_mul]
  norm_num
end D5.S1.Recurrence.HannaBilateral.OeisA363559PowerOfTwo
