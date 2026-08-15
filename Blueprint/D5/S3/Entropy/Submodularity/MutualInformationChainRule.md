# Mutual-Information Chain Rule

## Abstract

For a finite joint law, the information in a pair of observations splits into the information in the first observation and the remaining conditional information.

**Theorem 1.1 (Mutual information obeys the chain rule).**

$$\operatorname{mutualInformation}(p)= \operatorname{mutualInformation}(p_{XY})+ \operatorname{conditionalMutualInformation}(\operatorname{yFirstLaw}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pointwise nonnegative mass function on X times (Y times Z), the mutual information between X and the pair (Y,Z) is the mutual information between X and Y plus the conditional mutual information between X and Z given Y. Normalization is not needed for this identity.

The proof expands both mutual-information terms and the conditional term into entropy defects. Reindexing the Y-pivoted law and commuting the projected coordinates makes every marginal and joint-entropy term cancel algebraically.

**Theorem 1.2 (Adjoining an observation does not decrease information).**

$$\operatorname{mutualInformation}(p_{XY})\leq \operatorname{mutualInformation}(p).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_le_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative law, adjoining Z to the observation Y cannot reduce the mutual information with X. The difference is exactly the conditional mutual information between X and Z given Y.

The chain rule supplies the exact difference, while nonnegativity of conditional mutual information supplies its sign. No Markov assumption is required for this monotonicity statement.

**Theorem 1.3 (Pair-information equality is conditional factorization).**

$$\begin{gathered}\operatorname{mutualInformation}(p)= \operatorname{mutualInformation}(p_{XY}) \iff \\\forall y, p_{Y}(y) \neq 0 \Rightarrow p_{XZ \mid y}(x, z)= p_{X \mid y}(x)\times p_{Z \mid y}(z).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_pair_eq_iff_conditional_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair (Y,Z) carries exactly as much information about X as Y alone if and only if, on every Y-slice of nonzero mass, the conditional law of (X,Z) is the product of its X and Z marginals.

By the chain rule, equality of the two mutual informations is equivalent to vanishing conditional mutual information given Y. The frozen equality case for conditional mutual information then turns vanishing into the displayed slicewise factorization.

**Theorem 1.4 (Markov data-processing equality is reverse conditional factorization).**

$$\begin{gathered}\operatorname{Markov}(X, Y, Z) \Rightarrow (\operatorname{mutualInformation}(p_{XZ})= \operatorname{mutualInformation}(p_{XY}) \iff \\\forall z, p_{Z}(z) \neq 0 \Rightarrow p_{XY \mid z}(x, y)= p_{X \mid z}(x)\times p_{Y \mid z}(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_eq_of_markov_iff_conditional_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the X to Y to Z Markov hypothesis, equality in data processing holds exactly when X and Y are conditionally independent given every Z-value of nonzero mass. Thus lossless processing is characterized by a reverse conditional-product property.

The Markov hypothesis makes the conditional mutual information given Y vanish. The established gap identity then equates the data-processing gap with conditional mutual information given Z, whose zero case is precisely the displayed factorization of the conditional (X,Y)-law.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_chain_rule`
- Truth anchor: `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_eq_of_markov_iff_conditional_product`
- Truth anchor: `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_le_pair`
- Truth anchor: `D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_pair_eq_iff_conditional_product`
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../MutualInformationSymm.md)
- Dependency: [D5/S3/Entropy/Submodularity/MarkovDataProcessing](MarkovDataProcessing.md)
