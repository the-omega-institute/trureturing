# First-level inexactness on the weighted-crown interval

## Abstract

The first-level SDP is inexact throughout the open weighted-crown interval.

**Definition 1.1 (The open weighted-crown interval).**

$$claim = (\forall (n:\mathbb{N}), (3 \le n) \Rightarrow (\forall (x:\mathbb{R}), (\operatorname{L}\left(n\right) < x) \Rightarrow ((x < \operatorname{U}\left(n\right)) \Rightarrow (\operatorname{lambdaMax}\left(\operatorname{crownH}\left(n, x\right)\right) < \operatorname{npa1Value}\left(n, x\right)))))$$

*Formalization.* `D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.claim` (`✓ std3`).

*Citation.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

Appendix C.1, printed p. 33, verbatim: "The intermediate region (n + 2)²/4(n + 1) < x < (n + 2)/3 is left as an open problem, although numerics strongly suggest that SDP indeed fails in that region." The encoding quantifies every n ≥ 3 and every real x in the displayed open interval, and compares the nonzero-vector Rayleigh supremum with the real level-one moment optimum.

**Theorem 1.2 (The first-level SDP is inexact).**

$$\forall (n:\mathbb{N}), (3 \le n) \Rightarrow (\forall (x:\mathbb{R}), (\operatorname{L}\left(n\right) < x) \Rightarrow ((x < \operatorname{U}\left(n\right)) \Rightarrow (\operatorname{lambdaMax}\left(\operatorname{crownH}\left(n, x\right)\right) < \operatorname{npa1Value}\left(n, x\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/takahashi-et-al-2023-weighted-crown-npa1-gap` (proved) by `D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"takahashi-et-al-2023-weighted-crown-npa1-gap","declaration_gid":"D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Takahashi; C. Rayudu; C. Zhou; R. King; K. Thompson; O. Parekh (2023). *An SU(2)-symmetric Semidefinite Programming Hierarchy for Quantum Max Cut*. DOI: [10.48550/arXiv.2307.15688](https://doi.org/10.48550/arXiv.2307.15688). URL: <https://arxiv.org/abs/2307.15688v3>.

*Commentary.*

The feasible moment objective is strictly above n+1, while the literal Hamiltonian has Rayleigh supremum at most n+1. The upper interval endpoint is below 1+n/2, so the spectral bound applies to every point of the open interval.

## References

- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.claim`
- Truth anchor: `D5/S3/Quantum/Optimization/WeightedCrownFirstLevelGap.result`
- Dependency: [D5/S3/Quantum/Optimization/WeightedCrownMomentCertificate](WeightedCrownMomentCertificate.md)
