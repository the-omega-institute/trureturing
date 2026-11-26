# Tărnăuceanu’s Gauss image in the relative real topology

## Abstract

The exact Gauss values on C_(2^n) × C₂ rule out simultaneous closedness and discreteness in [1, ∞).

**Definition 1.1 (The group-theoretical Gauss invariant).**

$$\forall G \in \operatorname{FiniteGroup},\; f\left(G\right) = \frac{\sum_{H \le G} \Vert \operatorname{Aut}\left(H\right) \Vert}{\Vert G \Vert}$$

*Formalization.* `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gauss` (`✓ std3`).

*Citation.* Marius Tărnăuceanu (2026). *On some problems regarding a group-theoretical generalization of the Gauss formula*. DOI: [10.48550/arXiv.2611.34371](https://doi.org/10.48550/arXiv.2611.34371). URL: <https://arxiv.org/pdf/2611.34371v1#page=10>.

*Commentary.*

For a finite group G the numerator sums the order of the full automorphism group of every actual subgroup H of G. The sum includes the trivial subgroup and G itself. Both the summands and the denominator are cast to the reals. This is the invariant in §1 of arXiv:2611.34371v1.

**Definition 1.2 (The cyclic-product family).**

$$\forall n \in \mathbb{N},\; Family\left(n\right) = C_{2^{n}} \times C_{2}$$

*Formalization.* `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.Family` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marius Tărnăuceanu (2026). *On some problems regarding a group-theoretical generalization of the Gauss formula*. DOI: [10.48550/arXiv.2611.34371](https://doi.org/10.48550/arXiv.2611.34371). URL: <https://arxiv.org/pdf/2611.34371v1#page=10>.

*Commentary.*

The exponent n ranges over the natural numbers. C with a subscript m denotes a cyclic group of order m. At n = 0 the group is cyclic. The exact value theorem below uses positive exponents.

**Theorem 1.3 (Exact values for all positive exponents).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow f\left(C_{2^{n}} \times C_{2}\right) = 3 - 2^{-n}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gauss_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marius Tărnăuceanu (2026). *On some problems regarding a group-theoretical generalization of the Gauss formula*. DOI: [10.48550/arXiv.2611.34371](https://doi.org/10.48550/arXiv.2611.34371). URL: <https://arxiv.org/pdf/2611.34371v1#page=10>.

*Acknowledgement.* Georgiana Fasolă and Marius Tărnăuceanu (2023). *On a group-theoretical generalization of the Gauss formula*. DOI: [10.21136/CMJ.2022.0225-22](https://doi.org/10.21136/CMJ.2022.0225-22). URL: <https://arxiv.org/abs/2212.09055v1>.

*Commentary.*

Each element determines the cyclic subgroup it generates. Fibers of this map count generators, and a finite cyclic subgroup has as many generators as full automorphisms. The cyclic contribution therefore equals the group order, as in Equation (1) and the earlier proof of Theorem 1.1.

A subgroup with trivial intersection with the order-two projection kernel injects into the first cyclic factor and is cyclic. A noncyclic subgroup contains the kernel and is the full inverse image of a nontrivial subgroup of the first factor. There is exactly one actual noncyclic subgroup of type C_(2^k) × C₂ for each 1 ≤ k ≤ n.

For k = 1 an automorphism is an ordered pair of distinct nonidentity images, giving six possibilities. For k ≥ 2 the image of the long generator has a generating first coordinate and arbitrary second coordinate. The image of the order-two generator has first coordinate killed by squaring and nonidentity second coordinate. These choices give 2^(k+1) automorphisms. The resulting real numerator from noncyclic subgroups is 4·2^n − 2, and the group order is 2·2^n.

**Definition 1.4 (The image over all finite groups).**

$$I = \operatorname{Im}\left(f\right) \subseteq [1, \infty)$$

*Formalization.* `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gaussImage` (`✓ std3`).

*Citation.* Marius Tărnăuceanu (2026). *On some problems regarding a group-theoretical generalization of the Gauss formula*. DOI: [10.48550/arXiv.2611.34371](https://doi.org/10.48550/arXiv.2611.34371). URL: <https://arxiv.org/pdf/2611.34371v1#page=10>.

*Commentary.*

The image lies in the real subtype [1, ∞). The cyclic contribution gives the lower bound 1. The domain of the range map is the type of bundled finite groups. Every finite group in any carrier universe has an isomorphic representative there, and a group isomorphism preserves the sum by transporting the actual subgroups and their automorphism groups.

**Theorem 1.5 (Remark 3.4, closedness and discreteness).**

$$\neg \left(\operatorname{IsClosed}\left(I\right) \land \operatorname{DiscreteTopology}\left(I\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.image_not_closed_and_discrete` (`✓ std3`). ∎

*Resolves.* `Problems/tarnauceanu-2026-gauss-image-closed-discrete` (proved) by `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.image_not_closed_and_discrete`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tarnauceanu-2026-gauss-image-closed-discrete","declaration_gid":"D5/S3/FiniteGroups/Gauss/TarnauceanuImage.image_not_closed_and_discrete","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marius Tărnăuceanu (2026). *On some problems regarding a group-theoretical generalization of the Gauss formula*. DOI: [10.48550/arXiv.2611.34371](https://doi.org/10.48550/arXiv.2611.34371). URL: <https://arxiv.org/pdf/2611.34371v1#page=10>.

*Commentary.*

This proves the negative answer to the alternative in Remark 3.4 (arXiv:2611.34371v1, p. 10). Closedness is in the subtype [1, ∞), and discreteness refers to the image with the topology induced from that subtype.

The family values at exponents n + 1 converge to the relative point 3 and each differs from 3. Closedness would put 3 into the image. The sequence would then converge in the image itself, and the open singleton at 3 would have to contain every sufficiently late term.

## References

- Truth anchor: `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.Family`
- Truth anchor: `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gauss`
- Truth anchor: `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gaussImage`
- Truth anchor: `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.gauss_family`
- Truth anchor: `D5/S3/FiniteGroups/Gauss/TarnauceanuImage.image_not_closed_and_discrete`
- Dependency: [D5/S3/FiniteGroups/CyclicPrimePowerAction](../CyclicPrimePowerAction.md)
