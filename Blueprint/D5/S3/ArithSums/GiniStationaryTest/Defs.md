# Gini means and the stationary criterion

## Abstract

Gini comparison and stationary normalization.

**Definition 1.1 (The complete Gini mean).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.giniMean`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.giniMean` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For unequal parameters the existing Gini mean is used directly. For equal parameters the mean is the exponential of the power-weighted average of logarithms. On positive tuples both branches agree with the defining formulas.

**Definition 1.2 (The characteristic function).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.chi`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.chi` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The characteristic function is the divided difference of powers for distinct parameters, and the power times the logarithm for equal parameters.

**Definition 1.3 (Characteristic derivative).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.chiDeriv`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.chiDeriv` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The derivative is the real derivative of the characteristic function.

**Definition 1.4 (Comparison on an interval).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.Gamma`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.Gamma` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

Gamma records the parameter pairs for which the first Gini mean is at most the second on every tuple from the interval.

**Definition 1.5 (The normalized stationary criterion).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.stationaryTest`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.stationaryTest` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For each positive tuple with first Gini mean one, a common multiplier is required in all characteristic derivative equations. The criterion asks that the second Gini mean be at least one at every such tuple.

**Definition 1.6 (Characterization by stationary tuples).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Defs.claim`

*Formalization.* `D5/S3/ArithSums/GiniStationaryTest/Defs.claim` (`✓ std3`).

*Citation.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The claim quantifies over every n at least three and every nonempty positive interval whose quotient set has infimum zero. For every four real parameters, it asserts equivalence between comparison on the interval and the normalized stationary criterion.

## References

- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.Gamma`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.chi`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.chiDeriv`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.claim`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.giniMean`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Defs.stationaryTest`
- Dependency: [D5/S3/ArithSums/GiniMeanEndpointComparison](../GiniMeanEndpointComparison.md)
