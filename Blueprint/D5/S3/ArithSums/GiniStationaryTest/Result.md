# Stationarity does not ensure comparison

## Abstract

Normalized stationary tests do not characterize Gini comparisons on the positive half-line.

**Theorem 1.1 (A family in every dimension at least three).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Result.counterexample_family`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Result.counterexample_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For every natural n at least three, the parameters (r,s)=(1,0) and (p,q)=(2,-1) pass the normalized stationary test, while ((1,0),(2,-1)) is outside Gamma_n((0,infinity)). The stationary theorem applies to every positive normalized tuple and every multiplier satisfying the derivative equations. The tuple (1/2,1,...,1) reverses the required mean comparison. These statements refer to the same dimension and parameter pair.

**Theorem 1.2 (Refutation of the stationary characterization).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/grunwald-pales-2024-gini-stationary-test` (refuted) by `D5/S3/ArithSums/GiniStationaryTest/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"grunwald-pales-2024-gini-stationary-test","declaration_gid":"D5/S3/ArithSums/GiniStationaryTest/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

The full claim is false. Specialize it to n=3, I=(0,infinity), and the pair ((1,0),(2,-1)). This interval is nonempty and order connected. Its quotient set is exactly the positive half-line: every quotient is positive, and every positive y is y/1. The infimum of that half-line is zero. The claimed equivalence would turn the stationary test supplied by the family theorem into universal mean comparison, contradicting the other conjunct of that same family theorem. The equal-parameter branch in the claim uses the exponential definition, although this refutation uses only unequal parameters. No assertion about a scaled parameter family is needed.

## References

- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Result.counterexample_family`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Result.result`
- Dependency: [D5/S3/ArithSums/GiniStationaryTest/Stationary](Stationary.md)
- Dependency: [D5/S3/ArithSums/GiniStationaryTest/Witness](Witness.md)
