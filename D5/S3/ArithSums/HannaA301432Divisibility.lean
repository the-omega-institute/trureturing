/- GID: D5/S3/ArithSums/HannaA301432Divisibility
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaA301432Divisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Geometric binomial averages and Hanna's A301432 divisibility conjecture. -/

/-
admission_basis: open-problem-resolution (#21834; Proved)
escape_witness: none; the module is admitted by its settling result.
Direct pre-existing frozen dependencies: none.
Source/provenance qualification: https://github.com/the-omega-institute/trureturing/issues/21832#issuecomment-6562357166
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22143
Source: https://oeis.org/A301432/internal, COMMENTS and FORMULA.
The source series is literal; proofs use Mathlib preHilbertPoly composed with X^2.
a: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: claim, result.
claim: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none; consumers:
none; settling result.
Same-delivery dependency: D5/S3/ArithSums/HannaA301310Divisibility.falling_hasSum.
-/

import D5.S3.ArithSums.HannaA301310Divisibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.HannaA301432Divisibility


/-- OEIS A301432, third FORMULA line, interpreted as a convergent real series. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∑' k : ℕ, (3 : ℝ) ^ k * (Nat.choose (k ^ 2) n : ℝ) / (4 : ℝ) ^ (k + 1)

/-- OEIS A301432, first COMMENTS line: a(n) is divisible by 21 for n > 0. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, a n = (21 : ℝ) * (q : ℝ)



theorem result : claim := by
  intro n hn
  obtain ⟨q, hq⟩ := D5.S3.ArithSums.HannaA301310Divisibility.falling_hasSum n (by omega) 3
  refine ⟨q, ?_⟩
  norm_num only [Nat.cast_ofNat] at hq
  simpa only [a] using hq.tsum_eq


end D5.S3.ArithSums.HannaA301432Divisibility
