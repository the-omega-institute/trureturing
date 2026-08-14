# The Finite Mixture Entropy Bracket

## Abstract

Finite mixture entropy lies between weighted component entropy and that entropy plus the weight entropy; the upper equality case for pairwise disjoint supports is not covered in this stratum.

**Definition 1.1 (A mixture is the weighted component law).**

$$m(j)= \sum_{i} w(i) q_{i}(j).$$

*Formalization.* `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index carrier, the mixture mass at j is the sum of the component masses q_i(j), weighted by w(i). The definition itself does not impose normalization; the bracket theorems separately require w and every component to be probability laws.

**Definition 1.2 (The mixture joint law selects a component).**

$$P(i, j)= w(i) q_{i}(j).$$

*Formalization.* `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint law records both the selected component i and its output j. Its cell mass is w(i) q_i(j), which provides the common joint object used by the chain-rule and mutual-information arguments.

**Theorem 1.3 (The first mixture-joint marginal is the weight law).**

$$\operatorname{marginal}(P)= w.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_marginal_eq_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the joint law over j gives w(i), because each component q_i has unit total mass. This identity does not require w to be normalized or nonnegative.

**Theorem 1.4 (The second mixture-joint marginal is the mixture).**

$$\operatorname{marginal}(\operatorname{swap}(P))= m.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_swapped_marginal_eq_mixture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After swapping the two coordinates, marginalization over i is definitionally the weighted mixture. No probability-law hypotheses are needed for this finite-sum identity.

**Theorem 1.5 (Mixture-joint conditional entropy is weighted entropy).**

$$\operatorname{conditionalEntropy}(P)= \sum_{i} w(i) H(q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_conditionalEntropy_eq_weighted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conditioning the joint law on i recovers q_i whenever w(i) is nonzero, so its conditional-entropy contribution is w(i) H(q_i). If w(i) is zero, both sides of that slice identity vanish. Thus no restriction to the support of w is required.

**Theorem 1.6 (Weighted component entropy is below mixture entropy).**

$$\sum_{i} w(i) H(q_{i})\leq H(m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.weighted_entropy_le_mixture_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized nonnegative weights and normalized nonnegative components, conditioning the mixture joint law on its selector cannot have more entropy than the output marginal. Substituting the three joint identities gives the lower side of the mixture bracket.

**Theorem 1.7 (Mixture entropy is below weighted plus weight entropy).**

$$H(m)\leq H(w)+ \sum_{i} w(i) H(q_{i}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_le_weighted_add_weight_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chain rule expresses joint entropy as H(w) plus weighted component entropy. Applying the chain rule after swapping coordinates expresses the same joint entropy as H(m) plus a nonnegative conditional term, which proves the upper side of the bracket.

This stratum does not classify equality in this upper bound. In particular, the pairwise-disjoint-support characterization of the components is intentionally not claimed here.

**Theorem 1.8 (Mixture entropy gain is mutual information).**

$$H(m)- \sum_{i} w(i) H(q_{i})= I(P).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_sub_weighted_eq_mutual_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entropy gained by forgetting the selector is exactly the mutual information between selector and output in the mixture joint law. The identity follows by combining the joint chain rule with the frozen entropy decomposition of finite mutual information.

**Theorem 1.9 (Lower-bracket equality means identical active components).**

$$H(m)= \sum_{i} w(i) H(q_{i}) \Leftrightarrow\\\forall i, w(i)\neq 0 \Rightarrow q_{i}= m.$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_eq_weighted_iff_components_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the lower bracket is equivalent to zero mutual information for the mixture joint law. The finite independence characterization then says that the joint law is the product of its marginals. Cancelling each nonzero weight gives q_i = m, and the converse reconstructs the product law from those component equalities.

Zero-weight components are deliberately excluded from the conclusion. They contribute neither joint mass nor weighted entropy and therefore may be arbitrary without affecting equality.

## References

- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_conditionalEntropy_eq_weighted`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_marginal_eq_weight`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixtureJoint_swapped_marginal_eq_mixture`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_eq_weighted_iff_components_eq`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_le_weighted_add_weight_entropy`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.mixture_entropy_sub_weighted_eq_mutual_information`
- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyBracket.weighted_entropy_le_mixture_entropy`
- Dependency: [D5/S3/Entropy/ConditioningReducesEntropy](../ConditioningReducesEntropy.md)
- Dependency: [D5/S3/Entropy/EntropyNonneg](../EntropyNonneg.md)
- Dependency: [D5/S3/Entropy/MutualInformationIndependence](../MutualInformationIndependence.md)
- Dependency: [D5/S3/Entropy/MutualInformationSymm](../MutualInformationSymm.md)
