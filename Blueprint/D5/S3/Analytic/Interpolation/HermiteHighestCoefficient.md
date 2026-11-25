# Sharp quartic coefficient recovery from Hermite data

## Abstract

Sharp recovery of the quartic coefficient from two Hermite prefix differences.

Let x, y, z be the three nodes, in observation order. Put A = x² + xy + y², B = x³ + x²y + xy² + y³, C = x + y + z, and D = A + (x + y)z + z². For data from the cubic and quartic monomials the two rows are (A, B) and (C, D). Successive monic division gives these formulas for repeated nodes as well.

**Definition 1.1 (Explicit two-coordinate inverse).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.inverseTwo`

*Formalization.* `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.inverseTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With determinant Δ = AD − BC and data (d₀, d₁), the inverse coefficients are (Dd₀ − Bd₁)/Δ and (Ad₁ − Cd₀)/Δ.

**Theorem 1.2 (Two-sided inversion of the Newton data).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.weightedNewtonTail_two_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.weightedNewtonTail_two_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

For every triple of positive nodes, the explicit map is both a left and a right inverse to `D5/S3/Analytic/Interpolation/ConfluentPositiveSampling.weightedNewtonTail` with weight exponent 3 and two coefficient coordinates.

The determinant equals x²y² + xyz(x + y) + z²A, which is positive even at complete coalescence.

**Definition 1.3 (First weight).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight0`

*Formalization.* `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quartic coefficient uses weight −C/Δ on the first positive-order difference.

**Definition 1.4 (Second weight).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight1`

*Formalization.* `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quartic coefficient uses weight A/Δ on the second positive-order difference.

**Definition 1.5 (Absolute row sum).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum`

*Formalization.* `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The absolute values of the two weights sum to (C + A)/Δ at positive nodes.

**Theorem 1.6 (Optimal nodes in the positive unit cube).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nodes in (0, 1], the absolute row sum is at least 1. Equality holds exactly when all three nodes are 1. The determinant is at most twice each of A and C, and equality in the bound by twice A forces all three nodes to be 1.

**Theorem 1.7 (Exact scalar worst case).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestCoefficient_worst_case`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestCoefficient_worst_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over all scalar coefficient vectors whose two Newton observations have sup norm at most ε, for ε ≥ 0, the greatest absolute quartic coefficient is ε times the absolute row sum. The inverse of the data (−ε, ε) attains this value.

**Definition 1.8 (Matrix coefficient estimator).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.recoverHighest`

*Formalization.* `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.recoverHighest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the two signed weights to the two real two-by-two Hermite blocks and add the resulting matrices.

**Theorem 1.9 (Operator norm error with a within-derivative budget).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_error`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

In a nondegenerate closed interval let the three nodes be positive, with arbitrary repetitions. Suppose the matrix function has the form K + x³V₀ + x⁴V₁ + E(x) there, where K is constant. The remainder is twice continuously differentiable entrywise within the interval, and its within-derivative matrices of orders 1 and 2 have Euclidean operator norms bounded by B₀ and B₁.

If the reported blocks differ from `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail` by at most ε in the maximum of the two operator norms, the quartic coefficient error is at most ε times the absolute row sum plus |w₀|B₀ + |w₁|B₁/2, where w₀ and w₁ are the two inverse weights. In particular, exact data recover V₁ when the remainder vanishes, for any K.

The positive-order observations eliminate K. Testing the remainder block against two Euclidean vectors reduces each prefix to a scalar Hermite mean value identity. The resulting bound is B₀ for the first block and B₁/2 for the second.

**Theorem 1.10 (Rank-one attainment of the direct noise term).**

Lean statement: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such node triple, every constant K and every ε ≥ 0, take both coefficients along a rank-one matrix P of operator norm 1. A polynomial signal with remainder zero has exact data (−εP, εP) and quartic coefficient ε times the absolute row sum times P. With reported data zero, the direct noise is ε and the operator norm of the coefficient error attains the direct noise bound.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConfluentPositiveSampling.weightedNewtonTail`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestCoefficient_worst_case`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestRowSum_optimal`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight0`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.highestWeight1`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.inverseTwo`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_attained`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.matrixHermiteTail_highest_error`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.recoverHighest`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteHighestCoefficient.weightedNewtonTail_two_inverse`
- Dependency: [D5/S3/Analytic/Interpolation/ConfluentHermiteObservation](ConfluentHermiteObservation.md)
- Dependency: [D5/S3/Analytic/Interpolation/ConfluentPositiveSampling](ConfluentPositiveSampling.md)
