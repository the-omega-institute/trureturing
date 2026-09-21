# Antidiagonal Array and Source Series

## Abstract

The antidiagonal natural array and the normalized rational source series are uniquely determined, and their first-column coefficients agree after a one-step shift.

Mikhail Kurkov's A392095 defines the total natural function array: its zeroth row is one and each successor row uses the shifted entry and the finite sum over j from zero through k. The source is the normalized rational power series specified independently by Paul D. Hanna's A088713 equation F(x/F(x))=(1-x)^(-1). All coefficients are indexed from zero. The theorem result includes both uniqueness statements, the natural source sequence, and the shifted first-column identity. In the formulas, subst(F,U) means F(U), invOfUnit(F,1) is the multiplicative inverse of a constant-one series, and castQ embeds a natural number into the rationals. For b from N to N, B(b) denotes mk(m maps to castQ(b(m))). The construction and existence and uniqueness proofs are repository-derived; the recurrence, source equation and shifted-column assertion are the cited source statements.

$$
\begin{aligned}\operatorname{IsArray}\left(T\right) \iff (\forall k: \mathbb{N}, T\left(0, k\right) = 1) \land (\forall n: \mathbb{N}, \forall k: \mathbb{N}, T\left(n + 1, k\right) = T\left(n, k + 1\right) + \sum_{j = 0}^{k} (T\left(n, j\right) \cdot T\left(k - j, 0\right)))\\\operatorname{IsSource}\left(F\right) \iff (\operatorname{constantCoeff}\left(F\right) = 1) \land (\operatorname{subst}\left(F, X \cdot \operatorname{invOfUnit}\left(F, 1\right)\right) = \operatorname{invOfUnit}\left(1 - X, 1\right))\end{aligned}
$$

**Remark 1.1 (The antidiagonal array).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A392095, antidiagonal array and the shifted A088713 column*. URL: <https://oeis.org/A392095>.

*Commentary.*

The declaration array is the recursively constructed natural-valued two-index array. Its recursion is well founded by the lexicographic measure (n+k,n), with all finite-sum endpoints included.

**Remark 1.2 (The array predicate).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray` (`✓ std3`).

*Citation.* Mikhail Kurkov (2025). *OEIS A392095, antidiagonal array and the shifted A088713 column*. URL: <https://oeis.org/A392095>.

*Commentary.*

IsArray(T) records the zeroth-row equation and the full successor recurrence for every natural n and k, using the finite range k+1.

**Remark 1.3 (The normalized source predicate).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource` (`✓ std3`).

*Citation.* Paul D. Hanna (2003). *OEIS A088713, A(x/A(x)) = 1/(1-x)*. URL: <https://oeis.org/A088713>.

*Commentary.*

IsSource(F) requires constant coefficient one and the formal substitution equation F.subst(X times invOfUnit(F,1)) = invOfUnit(1-X,1).

**Remark 1.4 (The substitution operator).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

phi(F) is F.subst(X times invOfUnit(F,1)); it is defined without reference to the array.

**Remark 1.5 (Triangular source coefficients).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceCoeff is the recursively defined rational coefficient function obtained by forcing each coefficient of phi to equal the corresponding coefficient of the geometric series.

**Remark 1.6 (The independent source series).**

Lean statement: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries`

*Formalization.* `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceSeries is the power series whose coefficient at m is sourceCoeff(m).

**Theorem 1.7 (The complete array-source result).**

$$(\operatorname{IsArray}\left(\operatorname{array}\right)) \land ((\forall T: \mathbb{N}\to\mathbb{N}\to\mathbb{N}, (\operatorname{IsArray}\left(T\right)) \implies (T = \operatorname{array})) \land ((\operatorname{IsSource}\left(\operatorname{sourceSeries}\right)) \land ((\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSource}\left(F\right)) \implies (F = \operatorname{sourceSeries})) \land (\exists b: \mathbb{N}\to\mathbb{N}, (\operatorname{IsSource}\left(\operatorname{B}\left(b\right)\right)) \land ((\forall c: \mathbb{N}\to\mathbb{N}, (\operatorname{IsSource}\left(\operatorname{B}\left(c\right)\right)) \implies (c = b)) \land ((\operatorname{b}\left(0\right) = 1) \land ((\forall m: \mathbb{N}, \operatorname{coeff}\left(m, \operatorname{sourceSeries}\right) = \operatorname{castQ}\left(\operatorname{b}\left(m\right)\right)) \land (\forall n: \mathbb{N}, \operatorname{array}\left(n, 0\right) = \operatorname{b}\left(n + 1\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a392095-antidiagonal-source-series` (proved) by `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a392095-antidiagonal-source-series","declaration_gid":"D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result","resolution_kind":"proved"} -->

*Citation.* Mikhail Kurkov (2025). *OEIS A392095, antidiagonal array and the shifted A088713 column*. URL: <https://oeis.org/A392095>.

*Commentary.*

The result proves IsArray(array), uniqueness of every IsArray witness, IsSource(sourceSeries), uniqueness of every normalized source, existence and uniqueness of a natural source sequence, its zero coefficient, coefficient agreement with sourceSeries, and array(n,0)=b(n+1) for every natural n. Finite telescoping of the row recurrence identifies the column series after multiplication by X and addition of one. The remainder vanishes at each fixed degree, and source uniqueness gives the coefficient identity.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsArray`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.IsSource`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.array`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.phi`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceCoeff`
- Truth anchor: `D5/S1/Recurrence/Algebraic/AntidiagonalArraySourceSeries.sourceSeries`
- Dependency: [D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour](../Residue/QuotientThetaCompositionModFour.md)
