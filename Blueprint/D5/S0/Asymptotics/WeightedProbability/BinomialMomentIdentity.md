# Binomial Moment Identity

## Abstract

Every binomial moment of the finite capture count equals the total probability of all prescribed captured subsets of that size.

**Theorem 1.1 (Binomial moments enumerate prescribed captured sets).**

$$(\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \sum_{0\leq j\leq \lvert A \rvert} \operatorname{choose}(j,r) \operatorname{eventProbability}\left(q, \lvert C(f) \rvert = j\right) = \sum_{T\subseteq A, \lvert T \rvert= r} \operatorname{setCaptureProbability}\left(q, f, T\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity.exact_capture_count_binomial_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each sample, the capture-count sum selects its unique realized cardinality. The resulting binomial coefficient counts the r-element subsets of the captured-address finset by Finset.card_powersetCard.

Exchanging the finite sample and subset sums identifies membership in that powerset with simultaneous capture of every address in the prescribed set, yielding setCaptureProbability term by term.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/BinomialMomentIdentity.exact_capture_count_binomial_moment`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount](ExactCaptureCount.md)
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductSetCapture](FiniteProductSetCapture.md)
