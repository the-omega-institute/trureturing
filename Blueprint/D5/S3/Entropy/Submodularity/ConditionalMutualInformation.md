# Conditional Mutual Information

## Abstract

Finite conditional mutual information is the defect in conditional-entropy subadditivity and equals the strong-subadditivity entropy defect.

**Definition 1.1 (Conditional mutual information is the conditional-entropy defect).**

$$\operatorname{conditionalMutualInformation}(p):= \operatorname{conditionalEntropy}(p_{XY})+ \operatorname{conditionalEntropy}(p_{XZ})- \operatorname{conditionalEntropy}(p).$$

*Formalization.* `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditionalMutualInformation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a mass function on the right-nested product X times (Y times Z), conditional mutual information is the amount by which the sum of the XY and XZ conditional entropies exceeds the conditional entropy of the full law. The projections are the public interfaces established by strong subadditivity.

**Theorem 1.2 (Conditional mutual information is nonnegative).**

$$0\leq \operatorname{conditionalMutualInformation}(p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every normalized nonnegative finite law, conditional-entropy subadditivity says that the defining defect is nonnegative. The proof is a direct restatement of the frozen conditionalEntropy_pair_le_add interface and does not repeat its slicewise argument.

**Theorem 1.3 (Conditional mutual information is the entropy defect).**

$$\operatorname{conditionalMutualInformation}(p)= H(p_{XY})+ H(p_{XZ})- H(p)- H(p_{X}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_eq_entropy_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the entropy chain rule to the full law and both projections turns the conditional-entropy definition into the classical strong-subadditivity defect. Both projections have the same X marginal as the original law, so their marginal terms reduce to one surviving subtraction of H(X).

This identity needs only pointwise nonnegativity; normalization is not used by the entropy chain rule. It adds neither an equality characterization nor a Markov data-processing statement.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditionalMutualInformation`
- Truth anchor: `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_eq_entropy_defect`
- Truth anchor: `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_nonneg`
- Dependency: [D5/S3/Entropy/Submodularity/StrongSubadditivity](StrongSubadditivity.md)
