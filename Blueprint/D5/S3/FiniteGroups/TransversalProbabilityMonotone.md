# Normal extensions and common transversals

## Abstract

Common transversal probability increases when a subgroup is enlarged by a normal subgroup.

**Definition 1.1 (Two-sided transversal subsets).**

$$\forall G \in Type,\; [Group\left(G\right)] \forall H \in Subgroup\left(G\right),\; \forall K \in Subgroup\left(G\right),\; DT\left(H, K\right) = Subtype\left(\operatorname{fun} T : Set\left(G\right) \mapsto \operatorname{Subgroup.IsComplement}\left(T, (H : Set\left(G\right))\right) \land \operatorname{Subgroup.IsComplement}\left((K : Set\left(G\right)), T\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/TransversalProbabilityMonotone.DT` (`✓ std3`).

*Citation.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Definition 3.1(i), printed p. 8: “We denote by DT_G(H, K) the set of all left transversals for H in G, which are also right transversals for K in G.” The carrier is a subtype of Set G. Subgroup.IsComplement means that multiplication of the two subsets is bijective; T is not required to be a subgroup.

**Definition 1.2 (The normalized number of common transversals).**

$$\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \forall H \in Subgroup\left(G\right),\; \forall K \in Subgroup\left(G\right),\; \forall sameIndex \in \operatorname{H.index} = \operatorname{K.index},\; commonTransversalProbability\left(H, K, sameIndex\right) = \frac{(\operatorname{Nat.card}\left(DT\left(H, K\right)\right) : \mathbb{Q})}{(\operatorname{Nat.card}\left(H\right) : \mathbb{Q})^{\operatorname{H.index}}}$$

*Formalization.* `D5/S3/FiniteGroups/TransversalProbabilityMonotone.commonTransversalProbability` (`✓ std3`).

*Citation.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Definition 3.1(ii), printed p. 8: “We let P_G(H,K) ≔ |DT_G(H, K)|/|H|ⁿ, so that P_G(H, K) is the (Laplacian) probability that a left transversal for H in G is also a right transversal for K in G.” Here n = H.index = K.index. Nat.card counts subsets, and the quotient is rational.

**Definition 1.3 (The probability for one specified subgroup).**

$$\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \forall H \in Subgroup\left(G\right),\; P\left(H\right) = commonTransversalProbability\left(H, H, rfl\right)$$

*Formalization.* `D5/S3/FiniteGroups/TransversalProbabilityMonotone.P` (`✓ std3`).

*Citation.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Definition 3.1(ii), printed p. 8: “If H = K, we let P_G(H) ≔ P_G(H, H) be the probability that a left transversal for H in G is a two-sided one.” This quantity belongs to H; it is not the minimum over all subgroups.

**Definition 1.4 (Problem 5.2).**

$$claim = \left(\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \forall H \in Subgroup\left(G\right),\; \forall N \in Subgroup\left(G\right),\; \operatorname{N.Normal} \Rightarrow P\left(H\right) \le P\left(\operatorname{Max.max}\left(H, N\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/TransversalProbabilityMonotone.claim` (`✓ std3`).

*Citation.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

Problem 5.2, printed p. 37: “Suppose that H ≤ G and N ⊴ G, where G is finite. Is it then always true that P_G(H) ≤ P_G(HN) (GAP computations confirm this up to |G| = 200)?” The group G is arbitrary and finite. The product HN is H ⊔ N because N is normal. The equality question and the homomorphism consequence are separate from this inequality.

**Theorem 1.5 (The normal-extension inequality).**

$$\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] \forall H \in Subgroup\left(G\right),\; \forall N \in Subgroup\left(G\right),\; \operatorname{N.Normal} \Rightarrow P\left(H\right) \le P\left(\operatorname{Max.max}\left(H, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/TransversalProbabilityMonotone.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Aivazidis; M. Loukaki; T. W. Müller (2023). *On the common transversal probability in finite groups*. DOI: [10.48550/arXiv.2209.00986](https://doi.org/10.48550/arXiv.2209.00986). URL: <https://arxiv.org/abs/2209.00986v2>.

*Commentary.*

For each double coset, let t be its number of left H-cosets. Its contribution to the transversal count is t! times (|H|/t)^t. Normalizing gives the factor t!/t^t. This factor is nonnegative, at most one, and decreases with t. The quotient map from G/H to G/(H ⊔ N) maps every H-component onto the corresponding component for H ⊔ N: normality lets the N-factor pass through a group representative. Thus each upstairs component has at least the downstairs size. Comparing the factors within each nonempty fibre, and then multiplying, proves the displayed inequality.

## References

- Truth anchor: `D5/S3/FiniteGroups/TransversalProbabilityMonotone.DT`
- Truth anchor: `D5/S3/FiniteGroups/TransversalProbabilityMonotone.P`
- Truth anchor: `D5/S3/FiniteGroups/TransversalProbabilityMonotone.claim`
- Truth anchor: `D5/S3/FiniteGroups/TransversalProbabilityMonotone.commonTransversalProbability`
- Truth anchor: `D5/S3/FiniteGroups/TransversalProbabilityMonotone.result`
