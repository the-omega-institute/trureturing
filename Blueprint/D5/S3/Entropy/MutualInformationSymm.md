# Symmetry of Finite Mutual Information

## Abstract

Finite joint Shannon entropy and mutual information in nats are invariant under coordinate swap without distributional hypotheses.

**Theorem 1.1 (Joint entropy is invariant under coordinate swap).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\\operatorname{shannonEntropy}(((j, i)\mapsto p(i, j)))=\\\operatorname{shannonEntropy}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationSymm.entropy_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the two Fintype instances occur as hypotheses. Neither pointwise nonnegativity nor normalization is required. This is a strictly stronger hypothesis profile than that of every neighboring result in the bucket, all of which assume pointwise nonnegativity and some of which also assume normalization. The reason is structural: symmetry is a property of the finite sum's index set, not of the measure. Coordinate swap merely reindexes the sum, so no probabilistic axiom participates.

The equality is not definitional. In particular, rfl fails because the left side is summed over kappa times iota while the right side is summed over iota times kappa. Unfolding shannonEntropy and applying Fintype.sum_prod_type exposes the two nested finite sums; Finset.sum_comm then exchanges their order. This reindexing is the entire content of the proof, no more and no less.

**Theorem 1.2 (Finite mutual information is symmetric).**

$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] [\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\\operatorname{mutualInformation}(((j, i)\mapsto p(i, j)))=\\\operatorname{mutualInformation}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/MutualInformationSymm.mutual_information_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mutual-information symmetry has the same unconditional signature: only finiteness is assumed. A shorter composition through the frozen mutual_information_eq_entropy_sub identity would make symmetry nearly immediate from the entropy balance I = H(X) + H(Y) - H(X,Y). That route is deliberately not used. The entropy-balance identity assumes pointwise nonnegativity, so composing through it would contaminate an unconditional statement with an avoidable hypothesis. Direct unfolding preserves the actual strength of the result.

This equality is likewise not definitional, and rfl fails for the same mismatch between the index types kappa times iota and iota times kappa. After mutualInformation, klDivergence, and marginal are unfolded, Fintype.sum_prod_type and Finset.sum_comm discharge the coordinate reindexing. The swap also exchanges the two marginal factors in the reference product, and mul_comm restores their order. It does not make the swapped marginal equal to the first marginal: the two marginals exchange roles. The theorem contains exactly these reindexings and no additional probabilistic assertion.

Before this theorem, the bucket already contained mutual-information nonnegativity, the equivalence between zero mutual information and independence, the entropy decomposition of mutual information, the entropy chain rule, conditioning reduces entropy, and both equality cases of 0 <= H <= log card. Symmetry was the remaining elementary property of mutual information. The coordinate swap that every neighboring statement performs by hand in its own binder is now a named, reusable fact.

The units are nats because the underlying entropy and divergence use Real.log. Nothing is claimed about conditional mutual information, about a continuous or measure-theoretic analogue, or about systems with more than two coordinates.

## References

- Truth anchor: `D5/S3/Entropy/MutualInformationSymm.entropy_swap`
- Truth anchor: `D5/S3/Entropy/MutualInformationSymm.mutual_information_symm`
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
- Dependency: [D5/S3/Entropy/MutualInformation](MutualInformation.md)
