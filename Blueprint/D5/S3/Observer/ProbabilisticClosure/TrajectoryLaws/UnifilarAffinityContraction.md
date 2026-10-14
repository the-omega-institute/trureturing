# One distinguishing length and killed-pair contraction

## Abstract

One distinguishing length and killed-pair contraction

Let S be any finite state set. The nonnegative real symbol masses p(a,x) sum to one over both Boolean symbols at every a. The same successor map delta:S times Bool to S generates wordMass and endpoint from UnifilarPairSurvival. No stationarity, communication, positivity of symbols, aperiodicity or synchronization assumption is present. An empty pair set is allowed.

The finite distinguishing hypothesis says that for every distinct a,b there exists a natural length n at which their entire wordMass functions differ. This module proves the common finite-length consequence; OriginalUnifilarQuotient discharges that hypothesis for the actual complete-future-law quotient of the selected original presentation. It is an intermediate supplier, not an independently selected probability model.

**Theorem 1.1 (Nonnegative masses along the same trajectory).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.word_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.word_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state type S, p, delta and nonnegative p, natural n, state a and Boolean word of length n, wordMass(p,delta,n,a,w) is nonnegative. The proof inducts over this same word. OriginalUnifilarQuotient uses it inside the actual endpoint/MAP estimate.

**Theorem 1.2 (A common strict block controls every killed-pair power).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.finite_distinguishing_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.finite_distinguishing_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such p and delta with pairwise distinct finite-word laws, there exist a natural ell greater than zero and a real rho with 0 <= rho < 1. At this same ell, every distinct pair has different length-ell wordMass functions and Bhattacharyya affinity at most rho. For every natural n and ordered distinct pair s, the row sum of pairMatrix(p,delta) raised to n at s is at most rho raised to the natural quotient n/ell.

Word concatenation factors into prefix and suffix along the same deterministic endpoint. Summing all suffixes gives the prefix mass because every future word distribution is normalized. Select a distinguishing length for each of the finitely many pairs and take their maximum together with one. If two distributions agreed at that length, summing their suffixes would contradict the chosen shorter distinction. This proves a common length without a computable or efficient bound.

Apply the existing normalized Bhattacharyya upper bound and total-variation square inequality. A distinct pair has nonzero total variation by Metric.total_variation_eq_zero_iff, so affinity is strictly below one. The maximum over the finite pair affinities, together with zero for the empty-pair boundary, is an actual common rho below one. No estimated numerical constant is used.

pairMatrix_action and normalization bound each pair-matrix row by one. The exact existing pair_survival_word_affinity identifies its ell-th power row sum with affinity restricted to nonmerged words; this is at most the full distinguished-word affinity. A nonnegative matrix with row sums at most one and an ell-block row bound rho has n-th-power row sums at most rho^(n/ell): split off ell by strong induction, bound the short remainder by one, and multiply nonnegative rows. Natural division is exactly floor(n/ell). The proof keeps n=0 and zero symbol weights. If rho=0, zero to the zeroth power is one and all powers at n>=ell have zero row sum.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.finite_distinguishing_contraction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarAffinityContraction.word_nonneg`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival](UnifilarPairSurvival.md)
- Dependency: [D5/S3/TotalVariation/Hellinger](../../../TotalVariation/Hellinger.md)
