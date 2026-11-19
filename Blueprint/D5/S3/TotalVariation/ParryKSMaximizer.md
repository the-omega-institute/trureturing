# The bilateral Parry law is the unique entropy maximizer

## Abstract

Rigidity of entropy maximization for the bilateral forbidden-run shift.

**Theorem 1.1 (Equality in the bilateral Parry entropy bound).**

Lean statement: `D5/S3/TotalVariation/ParryKSMaximizer.bilateral_parry_maximizer`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryKSMaximizer.bilateral_parry_maximizer` (`✓ std3`). ∎

*Citation.* William Parry (1964). *Intrinsic Markov chains*. DOI: [10.1090/S0002-9947-1964-0161372-1](https://doi.org/10.1090/S0002-9947-1964-0161372-1). URL: <https://doi.org/10.1090/S0002-9947-1964-0161372-1>.

*Commentary.*

For every forbidden-run length k at least two, take a bilateral coding with the nearest-zero suffix property and a probability with the stationary Parry suffix cylinders at every integer origin. For each probability preserved by the unsigned shift, its full Kolmogorov–Sinai entropy is at most minus log p. Equality holds exactly when it equals the stated Parry probability. Here p is the reciprocal Perron root.

At each positive history length, compare the actual joint law of history and next suffix with the history marginal followed by one Parry transition. Stationarity cancels the expected endpoint log weights, so the relative entropy equals the difference between minus log p and the entropy increment. Forgetting the earliest suffix cannot increase this relative entropy. Each such difference therefore bounds the deficit in the full entropy rate from below.

At equality the finite relative entropies all vanish, fixing the law of the next suffix after every history. Each positive suffix has a unique possible predecessor, so stationarity and normalization determine the initial marginal. The common marginal and transitions determine all suffix cylinders. Each Boolean bit is recovered from its next suffix, and the bilateral Boolean cylinders determine the full measure.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryKSMaximizer.bilateral_parry_maximizer`
- Dependency: [D5/S3/Divergence/GibbsEquality](../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/DivergenceSupport/LogSumInequality](../DivergenceSupport/LogSumInequality.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost](../Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateGhost.md)
- Dependency: [D5/S3/TotalVariation/ParryKSEntropy](ParryKSEntropy.md)
