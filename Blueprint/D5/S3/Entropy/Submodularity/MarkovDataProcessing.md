# Markov Data Processing

## Abstract

For a finite Markov chain X to Y to Z, observing the channel output Z cannot reveal more about X than observing the intermediate variable Y.

**Theorem 1.1 (The mutual-information gap is a conditional-information gap).**

$$\operatorname{mutualInformation}(p_{XY})- \operatorname{mutualInformation}(p_{XZ})= \operatorname{conditionalMutualInformation}(\operatorname{zFirstLaw}(p))- \operatorname{conditionalMutualInformation}(\operatorname{yFirstLaw}(p)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_gap_eq_conditional_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pointwise nonnegative three-variable mass function, the difference I(X;Y) minus I(X;Z) equals I(X;Y given Z) minus I(X;Z given Y). The two conditional terms are represented by pivoting the right-nested law so that Z and Y respectively become the first, conditioning coordinate.

This is the general algebraic pin: normalization is not required. Expanding mutual information and conditional mutual information into entropy defects leaves only entropy invariance under the two coordinate pivots and the four projection identities.

**Theorem 1.2 (Channel-generated laws satisfy the Markov interface).**

$$\begin{gathered}(\forall y, \sum_{z} W(y, z)= 1) \Rightarrow\\\forall x, y, z, p(x, (y, z))\times p_{Y}(y)= p_{XY}(x, y)\times p_{YZ}(y, z).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MarkovDataProcessing.markov_of_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p(x,y,z) be generated as pXY(x,y) times W(y,z), where each row of W sums to one. Summing out Z recovers pXY, while the Y and YZ marginals share the same sum over X. These identities prove the exact cross-multiplied Markov interface used by the subsequent theorems.

No positivity or normalization assumption on pXY is needed for this algebraic witness. Thus the data-processing theorem's Markov hypothesis is verified for every row-normalized channel construction rather than silently assuming the desired conclusion.

**Theorem 1.3 (Markov mutual information obeys data processing).**

$$\operatorname{mutualInformation}(p_{XZ})\leq \operatorname{mutualInformation}(p_{XY}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_le_of_markov` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a normalized nonnegative law satisfying the X to Y to Z Markov interface, the conditional mutual information I(X;Z given Y) vanishes by the conditional-product equality characterization. The gap identity then identifies I(X;Y) minus I(X;Z) with I(X;Y given Z).

Conditional mutual information is nonnegative for the Z-pivoted law, so that remaining gap is nonnegative. Therefore the channel output Z retains no more mutual information about X than the intermediate Y.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/MarkovDataProcessing.markov_of_channel`
- Truth anchor: `D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_gap_eq_conditional_gap`
- Truth anchor: `D5/S3/Entropy/Submodularity/MarkovDataProcessing.mutual_information_le_of_markov`
- Dependency: [D5/S3/Entropy/Submodularity/ConditionalMutualInformation](ConditionalMutualInformation.md)
