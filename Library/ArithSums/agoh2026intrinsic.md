---
bibkey: agoh2026intrinsic
authors: Takashi Agoh
year: 2026
title: "An Intrinsic Factor of an Alternating Sum Involving Certain Rational Functions"
doi: 10.5281/zenodo.18154119
url: https://math.colgate.edu/~integers/aa9/aa9.pdf
claim: "The final conjecture characterizes the all-order alternating numerator factor property by monomials or simple real roots different from one."
strata_touched:
  - D5/S3/ArithSums/AgohAlternatingNumeratorRefutation
license: citation-only
triage: anchor
---

# Alternating rational-function numerators

The paper is INTEGERS 26 (2026), A9, published January 5, 2026.
For each natural n, Equation (3.1) defines
Q_n(X;f) = sum_{i=0}^n (-1)^i binom(n,i)/f(X^i).
The final printed page 9 states:

> Let f be a non-zero real-rooted polynomial in R[x]. Then, the numerator of Q_n(x; f) in (3.1) has 'at least' the factor (x-1)^n if and only if f is either a monomial or a polynomial that has only single roots different from 1.

The source uses typographic minus signs and quotation marks. The statement
above transliterates those characters without changing the words or quantifiers.
The all-n interpretation follows Theorem 3.1 and its context on printed page 7.
The numerator in the formal claim is the actual reduced numerator `RatFunc.num`.
Section 3 additionally assumes nonconstant f and f(1) != 0. The polynomial
(X-2)^2 satisfies these stronger conditions, is real-rooted and nonzero,
and has a repeated root at 2.

Equation (2.3) deletes a variable by its index. Repeated polynomial values
must retain their distinct indices. Its extension to f(X^i), followed by
coefficient expansion and the binomial theorem, proves the common numerator
is divisible by (X-1)^n. Since the common denominator evaluates to 1 for
(X-2)^2, Bezout coprimality transfers this factor to the reduced numerator.
The proof includes n=0 and does not use a finite-order boundary failure.

## Formal resolution

The frozen theorem
`D5/S3/ArithSums/AgohAlternatingNumeratorRefutation.result` has the closed type
`Not fullClaim`, with statement identity
`sha256:2a75da54a52fd95296805f384b83c5fe22e153eff87d5ed70694a9ce4125d3fb`.
Its witness is the actual polynomial f=(X-2)^2. The certificate proves that f
is nonzero, splits over the reals, is nonconstant, and satisfies f(1)=1. It
also proves for every natural n, including n=0, that (X-1)^n divides the
reduced `RatFunc.num` of the literal Equation (3.1) sum, while f is neither a
monomial nor a polynomial with only simple roots away from one. Thus the
formal result refutes the full printed equivalence under the source's stated
and contextual hypotheses, rather than a finite-order weakening.

The typed Scribe resolution binds this theorem to
`Problems/agoh-alternating-numerator-characterization` as `refuted`. This
records the frozen mathematical resolution; it does not assert repository
merge or KPI credit.

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.18154119
- Primary: https://math.colgate.edu/~integers/aa9/aa9.pdf
- Official version: https://zenodo.org/records/18154119
- Printed pages 4-5: Equation (2.3) and its alternating binomial use.
- Printed pages 6-7: Equation (3.1), Section 3 domain, and Theorem 3.1.
- Printed pages 8-9: repeated-root discussion and the final Conjecture.
- Nine-page primary PDF SHA256:
  `73a265d32948a5291347f457f457bf4981d908da2aee11a83a41bf032319fa81`.

## Provenance and bounded literature scope

The candidate and proof sketch were released publicly in project handoff
[7333, comment 5733245266](https://github.com/the-omega-institute/trureturing/issues/7333#issuecomment-5733245266).
The complete all-order target is preregistered in
[8702](https://github.com/the-omega-institute/trureturing/issues/8702).
These credits identify the preregistration and released route. No
first-discovery or publication-priority claim is made.

The supplied bounded source audit checked the journal volume, the official
Zenodo version and DataCite record, and exact-title/author/topic arXiv queries;
no accessible resolution was found in that scope. Crossref's DOI lookup did
not index this Zenodo DOI and its title results were noisy. OpenAlex was
rate-limited; Semantic Scholar yielded no usable DOI record. These are
explicit limits, not evidence of worldwide absence of a resolution.

Repository searches for Agoh, the DOI and the alternating-numerator statement
found no exact existing delivery. Prior pinned-Mathlib and bounded external
Lean searches found only unrelated Agoh-Giuga results, not this statement.
The proof directly reuses binomial expansion, polynomial composition and
coefficient APIs, `RatFunc.num_mul_eq_mul_denom_iff`, the remainder theorem,
and the coprime divisibility API. No external proof code is transplanted.
