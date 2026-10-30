/- GID: D5/S3/Combinatorics/HannaLambertW/OeisA386657LambertWEgfModSix
   generality: I
   mirror-B: D5/B/S3/Combinatorics/HannaLambertW/OeisA386657LambertWEgfModSix
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Lambert W coefficients and finite-ring binomial periodicity prove Hanna mod six. -/

/-
admission_basis: open-problem-resolution (#18668; Proved)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19849
Every theorem below has proof_shape: bind-only and escape_witness: none.
values: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: settling result.
Direct frozen dependencies (declaration identities on the merged base):
D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient
  statement_id: sha256:81f9e16808d9c491ff86a34e6bc2734ff65bb35128a1cae2aac5acffd2329b46
D5/S1/Recurrence/Residue/QuarticEGFModFour.F
  statement_id: sha256:00d1d435796f3af5e8009c9808ae0fd87d3c4afe48f8b0955596786da1bcb829
D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.subst_coeff is published here;
  its new public identity is to be read from the scoped freeze report.
The source definitions W and egf retain their displayed expressions.
The forward series is reused from QuarticEGFModFour.F.
Utility none: the conclusions are unbounded symbolic integrality and periodicity.
Finite-ring arithmetic and six initial values are consumed normalization steps.
-/

import D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix

set_option autoImplicit false

namespace D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix

open D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix (egf)

/-- A386657: the e.g.f. `∑_{n ≥ 0} (4^n x + LambertW(x))^n / n!`. -/
noncomputable def a (m : ℕ) : ℚ := egf 4 m

/-- A386657 ("Conjecture: for n >= 6, a(n) (mod 6) equals [1, 2, 3, 2, 3, 4] repeating."). -/
def claim : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∃ z : ℤ, (z : ℚ) = a n ∧ z % 6 = ([1, 2, 3, 2, 3, 4] : List ℤ).getD ((n - 6) % 6) 0

end D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix

namespace D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix
private theorem values : ∀ r : Fin 6, (D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ 4 (r.val+6)) % 6 =
    ([1, 2, 3, 2, 3, 4] : List ℤ).getD r.val 0 := by
  decide

theorem result : claim := by
  intro n hn
  refine ⟨D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ 4 n, ?_, (by
    rw [D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ_reduce 4 n hn]
    exact values ⟨(n-6)%6, Nat.mod_lt _ (by decide)⟩)⟩
  change (D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.closedZ 4 n : ℚ) = D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf 4 n
  exact (D5.S3.Combinatorics.HannaLambertW.OeisA386655LambertWEgfModSix.egf_closed 4 n).symm
end D5.S3.Combinatorics.HannaLambertW.OeisA386657LambertWEgfModSix
