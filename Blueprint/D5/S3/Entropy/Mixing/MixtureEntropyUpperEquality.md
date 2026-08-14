# Equality in the Upper Mixture-Entropy Bound

## Abstract

The upper finite mixture-entropy bound is sharp exactly when the positive-weight components have pairwise disjoint supports.

**Theorem 1.1 (Upper mixture-entropy equality means disjoint active supports).**

$$H(m)= H(w)+ \sum_{i} w(i) H(q_{i}) \Leftrightarrow \\\operatorname{PairwiseDisjoint}(\operatorname{supp}(w), (i\mapsto \operatorname{supp}(q_{i})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Mixing/MixtureEntropyUpperEquality.mixture_entropy_eq_weighted_add_weight_entropy_iff_pairwise_disjoint_supports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let w be a normalized nonnegative law on a finite selector carrier, and let every q_i be a normalized nonnegative law on a finite output carrier. The entropy of their mixture reaches weighted component entropy plus H(w) exactly when the supports of the components whose weights are nonzero are pairwise disjoint.

The support restriction on w is essential. A zero-weight component contributes no joint mass and no weighted entropy, so its support may overlap any other component without affecting equality. Positive-weight components, by contrast, must never assign nonzero mass to the same output.

For the selector-output joint law, the chain rule identifies the upper entropy gap with the conditional entropy of the selector given the output. The frozen zero-conditional-entropy characterization makes every positive-output slice a selector point mass. Such point masses are equivalent to each output belonging to at most one positive-weight component support, which is precisely the displayed pairwise disjointness condition.

## References

- Truth anchor: `D5/S3/Entropy/Mixing/MixtureEntropyUpperEquality.mixture_entropy_eq_weighted_add_weight_entropy_iff_pairwise_disjoint_supports`
- Dependency: [D5/S3/Entropy/ConditionalEntropyEquality](../ConditionalEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Mixing/MixtureEntropyBracket](MixtureEntropyBracket.md)
