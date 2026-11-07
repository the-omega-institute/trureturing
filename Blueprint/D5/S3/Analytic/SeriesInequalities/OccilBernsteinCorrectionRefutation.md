# A convex quadratic refutes both Bernstein corrections

## Abstract

The convex symmetric quadratic x² − x + 1/2 refutes both original Bernstein correction prescriptions at n = 2: their shared degree-4 normalized coefficient vector has middle entry −1/48.

**Definition 1.1 (The counterexample function).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.f`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.f` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

On [0,1], f(x) = (x − 1/2)² + 1/4 lies in (0,1], is convex, and is symmetric about 1/2. These hypotheses hold throughout the interval; no continuity hypothesis is needed.

**Definition 1.2 (The original Bernstein sample operator).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.B`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.B` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

For real u and natural n, B(n,u) sums u(j/n) times binom(n,j) X^j (1−X)^(n−j) over j = 0,...,n. Samples and polynomial scalars are real. All uses in the claim have n >= 2.

**Definition 1.3 (Range and convexity on the closed interval).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.admissible`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.admissible` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

The range is strictly positive and at most one for every x in [0,1]. Convexity is the inequality u(tx+(1−t)y) <= t u(x)+(1−t)u(y) for all x,y,t in [0,1]. Values of the real function outside this interval have no role.

**Definition 1.4 (An actual attained absolute maximum).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maxError`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maxError` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

Both clauses are required: every x in [0,1] has |B(n,u)(x)−u(x)| <= M, and some x in [0,1] attains equality. No continuity or supremum replaces this predicate.

**Definition 1.5 (The actual midpoint absolute error).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointError`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointError` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

This is |B(n,u)(1/2)−u(1/2)|, with no maximum premise.

**Definition 1.6 (The normalized degree-4 coefficient vector).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.coeff`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

The vector is [1/16,0,−1/48,0,1/16]. The normalization includes binom(4,j), as in the source; it is not a monomial coefficient vector.

**Definition 1.7 (A normalized representation at the specified degree).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.realization`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.realization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

The sum uses j in Fin(d+1), so it contains exactly j = 0,...,d. Each term is a(j) binom(d,j) X^j (1−X)^(d−j). Representation degree d does not assert that the ordinary polynomial degree equals d.

**Definition 1.8 (Nonnegative coefficients in that basis).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.nonnegativeCoefficients`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.nonnegativeCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

A polynomial has this property when it has a representation of the specified degree with all real coefficients nonnegative. The proof identifies every competing real representation uniquely by mapping it to the existing complex Bernstein-independent family and using the injective real embedding.

**Definition 1.9 (The full universal attained-maximum coefficient assertion).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maximumBranch`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maximumBranch` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

For every admissible real function, every integer k >= 1 and every pair of actual attained maxima M,N at n = 2^k and 2n, the unmodified increment (B(2n,u)−N)−(B(n,u)−M) must have nonnegative normalized coefficients at representation degree exactly 2n.

**Definition 1.10 (The full universal symmetric midpoint coefficient assertion).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointBranch`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointBranch` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

For every admissible real function symmetric on [0,1], and every integer k >= 1, subtract the actual midpoint absolute errors from B at n = 2^k and 2n. The increment must have nonnegative normalized coefficients at representation degree exactly 2n. There is no maximum premise.

**Definition 1.11 (The conjunction of the two coefficient assertions).**

$$claim \Leftrightarrow \left(maximumBranch \land midpointBranch\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.claim` (`✓ std3`).

*Citation.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

Occil's first item after the final Prove or disprove in Other Questions asks for both correction prescriptions to converge from below with nonnegative Bernstein increment coefficients. The claim is precisely the conjunction of their universal coefficient requirements. Each is a necessary clause of the corresponding original branch, independently of the unspecified convergence topology. A positive coefficient result alone would not prove convergence.

**Theorem 1.12 (Both original prescriptions fail at n = 2).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/occil-convex-bernstein-corrections` (refuted) by `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"occil-convex-bernstein-corrections","declaration_gid":"D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Occil (2026). *Open Questions on the Bernoulli Factory Problem*. URL: <https://peteroupc.github.io/bernreq.html#Other_Questions>.

*Commentary.*

For f(x) = x²−x+1/2, B₂f = (X²−X)/2+1/2 and B₄f = 3(X²−X)/4+1/2. The errors are x(1−x)/2 and x(1−x)/4 on the entire interval, with actual maxima 1/8 and 1/16 attained at 1/2; these also equal the midpoint errors. Both increments are 1/16−X(1−X)/4 = (X−1/2)²/4. The exact degree-4 normalized coefficients are [1/16,0,−1/48,0,1/16]. Uniqueness excludes any nonnegative representation. Each universal coefficient assertion is therefore false, so their conjunction is false. This refutes both full original conjunctions through their coefficient clauses without a claim against convergence itself. Uniqueness follows from complex Bernstein independence via the injective real embedding.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.B`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.admissible`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.claim`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.coeff`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.f`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maxError`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.maximumBranch`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointBranch`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.midpointError`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.nonnegativeCoefficients`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.realization`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/OccilBernsteinCorrectionRefutation.result`
- Dependency: [D5/S3/Observer/BlockStructure/CommonDenominatorPolynomialBasis](../../Observer/BlockStructure/CommonDenominatorPolynomialBasis.md)
