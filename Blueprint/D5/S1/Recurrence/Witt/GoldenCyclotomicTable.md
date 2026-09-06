# Golden Cyclotomic Table Through Degree Five

## Abstract

The golden admissible-word series has the stated signed cyclotomic factors through total degree five.

**Theorem 1.1 (The cleared cyclotomic factors agree in every low bidegree).**

$$\forall a, b \in \mathbb{N},\ a + b \leq 5 \Rightarrow \operatorname{convolution}\left(goldenPrefix, positiveWittFactors, a, b\right) = \operatorname{negativeWittFactors}\left(a, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/GoldenCyclotomicTable.golden_cyclotomic_table_degree_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix coefficients are computed from the frozen admissible-word degree map. Bivariate convolution is the exact Cauchy product, so the equality checks the cleared formal factorization coefficient by coefficient rather than through numerical evaluation.

The positive factors occur at (1,0), (0,1), (2,1), (1,2), (4,1), (3,2), and (2,3). The negative factors occur at (2,0), (0,2), (3,1), and (2,2). Every omitted bidegree of total degree at most five has zero exponent.

In particular, this proves the previously unfrozen entries e22 = -1 and e41 = e32 = e23 = 1, while agreeing with the frozen pure and first-row laws on their overlap.

The source theorem also reports an all-stage zeta cascade and numerical staircase certificates. Those analytic and empirical clauses are not consequences of the current frozen API. The formal statement is therefore the exact finite cyclotomic core through total degree five and makes no unproved convergence or continuation claim.

The escape witness is the public coefficient identity itself: kernel reduction computes twenty-one new finite convolution equalities from the canonical word degrees. It cannot be obtained by projection or normalization of the frozen bivariate functional equation.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/GoldenCyclotomicTable.golden_cyclotomic_table_degree_five`
- Dependency: [D5/S1/Recurrence/BivariateWordSeries](../BivariateWordSeries.md)
