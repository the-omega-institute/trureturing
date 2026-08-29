# Expected Posterior Entropy Reduction

## Abstract

Finite experiment information gain is exactly expected posterior entropy reduction.

**Theorem 1.1 (Information gain equals expected posterior entropy reduction).**

$$\forall X \in Type, Y \in Type, pi \in X \to Real, W \in X \to \left(Y \to Real\right),\; \left(\left(\operatorname{Fintype}\left(X\right) \land \operatorname{Fintype}\left(Y\right)\right) \land \left(\left(\forall y \in Y, x \in X,\; 0 \le pi\left(x\right) \cdot W\left(x, y\right)\right) \land \left(\forall x \in X,\; \sum_{y} W\left(x, y\right) = 1\right)\right)\right) \Rightarrow \operatorname{informationGain}\left(W, pi\right) = \operatorname{shannonEntropy}\left(pi\right) - \operatorname{expectedPosteriorEntropy}\left(W, pi\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.information_gain_eq_expected_entropy_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state and observation carriers are finite. The induced joint weights are nonnegative, and each channel row has total mass one.

The information gain is mutual information of the observation-first joint law. The posterior is the repository's totalized Bayes posterior, weighted by the output marginal.

Prior normalization is not needed for this finite algebraic identity. Empty carriers and zero-probability output slices are included.

**Theorem 1.2 (Joint nonnegativity is necessary).**

$$\operatorname{let} pi : \operatorname{Option}\left(Bool\right) \to Real := (x \mapsto \operatorname{if}\left(x = none, -2, 1\right));\\{}\operatorname{let} W : \operatorname{Option}\left(Bool\right) \to \left(Unit \to Real\right) := (x, y \mapsto 1);\\{}\left(\forall x \in \operatorname{Option}\left(Bool\right),\; \sum_{y} W\left(x, y\right) = 1\right) \land \left(\left(\neg \left(\forall y \in Unit, x \in \operatorname{Option}\left(Bool\right),\; 0 \le pi\left(x\right) \cdot W\left(x, y\right)\right)\right) \land \operatorname{informationGain}\left(W, pi\right) \ne \operatorname{shannonEntropy}\left(pi\right) - \operatorname{expectedPosteriorEntropy}\left(W, pi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.joint_nonnegativity_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A three-state signed prior with masses minus two, one, and one is observed through a normalized singleton-output channel.

The induced joint has a negative cell and zero output mass. Under the repository's totalized logarithm and division conventions, the entropy-reduction identity fails.

**Theorem 1.3 (Channel normalization is necessary).**

$$\operatorname{let} pi : Unit \to Real := (x \mapsto 1);\\{}\operatorname{let} W : Unit \to \left(Unit \to Real\right) := (x, y \mapsto 2);\\{}\left(\forall y \in Unit, x \in Unit,\; 0 \le pi\left(x\right) \cdot W\left(x, y\right)\right) \land \left(\left(\neg \left(\forall x \in Unit,\; \sum_{y} W\left(x, y\right) = 1\right)\right) \land \operatorname{informationGain}\left(W, pi\right) \ne \operatorname{shannonEntropy}\left(pi\right) - \operatorname{expectedPosteriorEntropy}\left(W, pi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.channel_normalization_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton prior of mass one and a singleton channel row of mass two give nonnegative induced joint weights.

The row is not normalized, and its mutual information is nonzero under the repository definition while both displayed entropy terms vanish.

## References

- Truth anchor: `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.channel_normalization_is_necessary`
- Truth anchor: `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.information_gain_eq_expected_entropy_reduction`
- Truth anchor: `D5/S3/Entropy/Observation/ExpectedPosteriorEntropyReduction.joint_nonnegativity_is_necessary`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](../ConditionalEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformationEntropy](../MutualInformationEntropy.md)
