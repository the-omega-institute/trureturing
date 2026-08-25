# Actual-Posterior Information Gain Can Increase

## Abstract

A realized posterior can increase the information value of a deterministic experiment.

**Theorem 1.1 (Deterministic experiments need not have adaptive diminishing returns).**

$$\begin{gathered}X = \operatorname{Option}\left(Bool\right),\\{}\mu(none) = \frac{1}{2}, \forall b: Bool, \mu(some(b)) = \frac{1}{4},\\{}A(none) = true, \forall b: Bool, A(some(b)) = false,\\{}B(some(true)) = true, B(none) = false, B(some(false)) = false,\\{}muPost(x) = \operatorname{if}\left(A(x) = false, \frac{\mu(x)}{\operatorname{pushforward}\left(A, \mu\right)(false)}, 0\right),\\{}P(x, a, b) = \operatorname{if}\left((a, b) = (A(x), B(x)), 1, 0\right):\\{}{{\forall x: X, 0 \le \mu(x)} \land \sum_{x} \mu(x) = 1} \land\\{}0 < \operatorname{pushforward}\left(A, \mu\right)(false) \land\\{}{{\forall x: X, 0 \le muPost(x)} \land \sum_{x} muPost(x) = 1} \land\\{}{\forall x: X, a, b: Bool, P(x, a, b) = {\sum_{bPrime} P(x, a, bPrime)} \times {\sum_{aPrime} P(x, aPrime, b)}} \land\\{}\operatorname{mutualInformation}\left(\operatorname{readoutTargetLaw}\left(\mu, B, id\right)\right) < \operatorname{mutualInformation}\left(\operatorname{readoutTargetLaw}\left(muPost, B, id\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease.actual_posterior_information_gain_can_increase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hidden carrier has exactly three states. One state has prior mass one half and the other two have mass one quarter each. The first deterministic readout isolates the high-mass state, while the second isolates one of the remaining states.

The displayed posterior is the Bayes restriction to the positive-probability branch on which the first readout excludes the high-mass state. Both the prior and posterior are displayed as normalized nonnegative laws.

At each hidden state the joint deterministic output law factors into its two marginals. Nevertheless, the mutual information supplied by the second readout is strictly larger after the realized first-readout branch.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease.actual_posterior_information_gain_can_increase`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../Communication/TranslationLossMonotonicity.md)
