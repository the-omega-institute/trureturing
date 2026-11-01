/- GID: D5/S3/ArithSums/HannaA301311Divisibility
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaA301311Divisibility
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Geometric binomial averages and Hanna's A301311 divisibility conjecture. -/

/-
admission_basis: open-problem-resolution (#21833; Proved)
escape_witness: none; the module is admitted by its settling result.
Direct pre-existing frozen dependencies: none.
Source/provenance qualification: https://github.com/the-omega-institute/trureturing/issues/21832#issuecomment-6562357166
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22143
Source: https://oeis.org/A301311/internal, COMMENTS and FORMULA.
The source series is literal; proofs use Mathlib preHilbertPoly composed with X^2.
a: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies: none;
consumers: claim, result.
claim: proof_shape: bind-only (definition); escape_witness: none; Direct pre-existing frozen dependencies:
none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; Direct pre-existing frozen dependencies: none; consumers:
none; settling result.
Same-delivery dependency: D5/S3/ArithSums/HannaA301310Divisibility.rising_hasSum.
-/

import D5.S3.ArithSums.HannaA301310Divisibility

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.HannaA301311Divisibility


/-- OEIS A301311, third FORMULA line; the n = 0 binomial coefficient is one. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∑' k : ℕ, (2 : ℝ) ^ k * (Nat.choose (k ^ 2 + n - 1) n : ℝ) /
    (3 : ℝ) ^ (k + 1)

/-- OEIS A301311, second COMMENTS line: a(n) is divisible by 10 for n > 0. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ q : ℤ, a n = (10 : ℝ) * (q : ℝ)



theorem result : claim := by
  intro n hn
  obtain ⟨q, hq⟩ := D5.S3.ArithSums.HannaA301310Divisibility.rising_hasSum n (by omega) 2
  refine ⟨q, ?_⟩
  norm_num only [Nat.cast_ofNat] at hq
  simpa only [a] using hq.tsum_eq


end D5.S3.ArithSums.HannaA301311Divisibility
