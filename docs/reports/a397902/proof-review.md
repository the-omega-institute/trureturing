# A397902 proof assessment

Origin: local `lean4` skill, one Codex implementation worker. The earlier and
later checkpoints are one continuing worker history, not independent reviews.
User input supplied the target, numerical expectations and bounded literature
adjudication. This worker reran the probes/searches and performed the Lean work.
There are zero independent review votes; these assessments are the implementer's.

## Public theorem assessment

Let M denote `D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport`.
Private helpers are inlined when assessing proof shape. These are proposed
semantic assessments, not verdicts computed from dependency counts.

| Public theorem | proof_shape | Direct frozen D5 dependencies after private expansion | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| M.generating_equation | content | none | approximation_stable, normalized_change | escape-witness |
| M.integer_exists_unique | content | none | approximation_stable, normalized_unique | escape-witness |
| M.hanna_conjecture | content | C.binary_catalan and C.catalanSeries, identified below | candidate_even, candidate_odd, power_diagonal_zero | escape-witness |

C is `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`.
The exact frozen prerequisites are:

- C.binary_catalan: `sha256:af01ed7b8646d5e823f1a3147c91cb613eb1eb6b7c1ec7ccf05a09b3b31bb57c`.
- C.catalanSeries (definition): `sha256:18682fb8cb0da671f4d582ed20b987849bfe41eba3bfcb33e1279f655fae00a0`.

The first two theorems use standard Mathlib power-series and ring facts;
there is no D5 frozen result being instantiated to construct this solution.
Their proofs feed the last theorem through the explicit consumer-to-prerequisite
edges hanna_conjecture -> integer_exists_unique and generating_equation.
The public definitions generatingSeries, DefiningEquation and a name the witness,
source predicate and coefficient function; they assert no additional theorem.

## Four witness requirements

For generating_equation and integer_exists_unique:

1. **Elaborated dependency closure:** the repository proof-edges tool, which
   expands auxiliary constants, places approximation_stable and normalized_change
   in both closures, and normalized_unique in the uniqueness closure.
2. **Not a frozen projection or normalization:** stabilization is an induction
   on the precision of successive integer approximations. The unit multiplier
   is proved using power-difference and derivative coefficient arguments. No
   imported theorem supplies that recurrence's stabilization or uniqueness.
3. **Not definitionally the conclusion:** these are statements about agreement
   of approximations and normalized residual differences over an arbitrary
   commutative ring. Neither is the integer OEIS existence assertion or the
   original inverse-denominator equation.
4. **Live path:** stabilization gives solution_agree -> solution_fixed ->
   solution_normalized. Exact normalization gives the original row equation.
   normalized_unique is applied to an arbitrary integer solution to establish
   equality with the constructed series. The supplied proof terms use these
   facts to derive the result, rather than discarding an added conjunct.

For hanna_conjecture:

1. **Elaborated dependency closure:** candidate_even, candidate_odd and
   power_diagonal_zero occur through solution_parity -> solution_mod_two ->
   candidate_normalized. This was checked against the kernel edge output.
2. **Not a frozen projection or normalization:** candidate_even requires the
   induction that repeatedly halves the degree in coeff(n,F^(2*n*t));
   candidate_odd combines the even/odd decomposition with the derivative of F.
   The existing Catalan theorem only gives U's support and contains no normalized
   square-exponent row condition for this series.
3. **Not definitionally the conclusion:** the witnesses assert vanishing of
   normalized residuals for arbitrary binary series satisfying two algebraic
   identities. They do not assert the four-family integer support classification.
4. **Live path:** row vanishing identifies the binary candidate by normalized
   uniqueness; candidate_coeff then reduces the coefficient to U_support;
   binary_catalan and support_arithmetic finish the classification. Without
   candidate row vanishing this proof cannot identify the OEIS series with U.

The proposed v2 witness was recorded before its Lean implementation in attempt.md:
exact derivative normalization plus binary candidate row vanishing. The implemented
route retains that normalization rather than assuming a 2-adic precision bound.
In particular no cancellation of an even square is attempted after reduction.

## Utility and source boundary

`utility: none`: every assertion is an unbounded symbolic statement. The module
contains no coefficient table, bounded enumeration, certified positive numerical
instance, checker or numeric reduction. The generic diagonal proof uses induction
for all positive degrees; arithmetic tactics only close symbolic identities and
index bounds. The numerical recurrence probe is not a frozen result.

The source predicate quantifies over PowerSeries Z, requires constant coefficient
zero and every m>1 row, and uses exponent m squared. The denominator has constant
one, so its invOfUnit is exactly formal division by 1-m squared X. Existence is
proved over Z directly; the theorem is not conditional on an unproved rational
integrality claim. The final theorem quantifies over any A satisfying this predicate
and every natural n>2, with exactly the four alternatives and k>1.

## Not claimed

No global absence of prior proofs or priority claim. The literature status was
open only within the recorded effective searches. Failed/non-specific queries
are not negative evidence. No conclusion is transferred from another OEIS family.
No independent adversarial review, no new axiom, no new source atom, no coverage
edge and no theory ingestion are claimed. Pages not fetched are marked
ASSUMED-UNVERIFIED in the source/search notes. Kernel validation and the dependency
extractor do not themselves certify the semantic proof-shape assessment above.
