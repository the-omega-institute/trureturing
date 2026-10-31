# A126156 and the Totient Period Bound

## Abstract

The square-root secant sequence has no eventual period dividing the totient at modulus four.

The source is OEIS A126156, revision 110, NAME and the third COMMENTS entry; the entry has no page numbers. The even coefficient at index n is scaled by (2n)!. A rational power series A represents the positive square root through constant coefficient one and A squared times cosSqrtTwo equal to one.

All sequence indices, moduli, onsets and periods are natural numbers. An integer z expresses divisibility in the rational coefficient field. Nat.div is natural-number division; the fraction in cosSqrtTwo is rational division. The type annotations in parentheses show the casts to the rationals.

**Definition 1.1 (The rational cosine series).**

$$cosSqrtTwo = \operatorname{PowerSeries}.\operatorname{mk}\left((j: \mathbb{N} \mapsto \operatorname{ite}\left(\operatorname{Even}\left(j\right), \frac{((-2: \mathbb{Q}))^{\operatorname{Nat}.\operatorname{div}\left(j, 2\right)}}{(\operatorname{Nat}.\operatorname{factorial}\left(j\right): \mathbb{Q})}, 0\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.cosSqrtTwo` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A126156: eventual periods dividing the Euler totient*. URL: <https://oeis.org/A126156>.

*Commentary.*

The coefficient at an even j is (-2) raised to j divided by two, divided by j factorial; the coefficient at an odd j is zero. This is cos(sqrt(2)*x) over the rationals.

**Definition 1.2 (The square-root secant equation).**

$$\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceEGF}\left(A\right) = ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(A\right) = 1) \land ((A)^{2} \cdot cosSqrtTwo = 1))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.IsSourceEGF` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A126156: eventual periods dividing the Euler totient*. URL: <https://oeis.org/A126156>.

*Commentary.*

Expansion of e.g.f. sqrt(sec(sqrt(2)*x)), showing coefficients of only the even powers of x. (OEIS A126156, revision 110, NAME; no page number.) The series has constant coefficient one and its square multiplied by cosSqrtTwo is one. These equations select the formal square root with positive constant term.

**Definition 1.3 (Bala's eventual period assertion).**

$$claim = ((\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceEGF}\left(A\right)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsSourceEGF}\left(A\right)) \implies (\forall (k: \mathbb{N}), (0 < k) \implies (\exists (N: \mathbb{N}), \exists (p: \mathbb{N}), (0 < p) \land ((p \mid \operatorname{Nat}.\operatorname{totient}\left(k\right)) \land (\forall (n: \mathbb{N}), (N \le n) \implies (\exists (z: \mathbb{Z}), (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot (n + p)\right): \mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(2 \cdot (n + p), A\right) - (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot (n)\right): \mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(2 \cdot (n), A\right) = (k: \mathbb{Q}) \cdot (z: \mathbb{Q}))))))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.claim` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A126156: eventual periods dividing the Euler totient*. URL: <https://oeis.org/A126156>.

*Commentary.*

Conjecture: the sequence {a(n)} reduced modulo a positive integer k is eventually periodic with the period dividing phi(k), where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Mar 01 2026 (OEIS A126156, revision 110, third COMMENTS entry; no page number.) The expression (2n)! times PowerSeries.coeff(2n,A) is the zero-based sequence a(n). The assertion includes existence of such an A and quantifies over every such A, every positive modulus k, an eventual onset N and a positive period p dividing Nat.totient(k).

**Theorem 1.4 (The totient period assertion is false).**

$$\neg ((\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsSourceEGF}\left(A\right)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsSourceEGF}\left(A\right)) \implies (\forall (k: \mathbb{N}), (0 < k) \implies (\exists (N: \mathbb{N}), \exists (p: \mathbb{N}), (0 < p) \land ((p \mid \operatorname{Nat}.\operatorname{totient}\left(k\right)) \land (\forall (n: \mathbb{N}), (N \le n) \implies (\exists (z: \mathbb{Z}), (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot (n + p)\right): \mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(2 \cdot (n + p), A\right) - (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot (n)\right): \mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(2 \cdot (n), A\right) = (k: \mathbb{Q}) \cdot (z: \mathbb{Q}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala126156` (refuted) by `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala126156","declaration_gid":"D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2026). *OEIS A126156: eventual periods dividing the Euler totient*. URL: <https://oeis.org/A126156>.

*Commentary.*

For each series satisfying the square-root secant equation, the scaled even coefficients are integers and odd, and their two-step differences equal four times an integer plus two. Integer derivative polynomials give the two-step identity, and induction gives oddness. At modulus four the totient is two; the permitted positive periods are one and two. Period one would imply period two by adding consecutive differences. The two-step identity excludes either period at every onset. This does not settle a bound of twice the totient or a general assertion for odd moduli.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.IsSourceEGF`
- Truth anchor: `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.cosSqrtTwo`
- Truth anchor: `D5/S1/Recurrence/Periodic/SquareRootSecantTotientPeriodRefutation.result`
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](../Residue/IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)
