# Subgroup Conjugacy Ratios

## Abstract

Whole subgroup lattices and their inner-conjugacy quotients multiply over coprime products.

**Definition 1.1 (The observable on actual groups).**

$$\forall G \in Typeu,\; Group\left(G\right) \to ratio\left(G\right)=divide\left(rationalCast\left(classCount\left(G\right)\right), rationalCast\left(latticeCount\left(G\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SubgroupConjugacyRatio.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mihai-Silviu Lazorec and Marius Tărnăuceanu (2025). *On the number of conjugacy classes of subgroups of a finite group*. DOI: [10.48550/arXiv.2508.14267](https://doi.org/10.48550/arXiv.2508.14267). URL: <https://arxiv.org/html/2508.14267v2>.

*Commentary.*

For a group G, latticeCount G is Nat.card (Subgroup G), including the trivial subgroup and G. SubgroupClasses G is the quotient of Subgroup G by the orbit relation for ConjAct G, acting by inner conjugation. classCount G is its Nat.card. The rational ratio divides these two cardinalities. On finite groups the denominator is positive, since the whole subgroup lattice contains the trivial subgroup. Section 1 of Lazorec and Tărnăuceanu defines this observable on finite groups. The displayed declaration defines a rational-valued function for any group; its interpretation here as the source ratio is on finite groups.

**Definition 1.2 (The exact rational attainment question).**

$$RationalAttainment\left(\right)=\forall a \in Integers,\; \forall b \in Integers,\; 1\le a \to \left(a<b \to \left(\exists W \in FiniteGroup\left(\right),\; b*integerCast\left(classCount\left(Carrier\left(W\right)\right)\right)=a*integerCast\left(latticeCount\left(Carrier\left(W\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SubgroupConjugacyRatio.RationalAttainment` (`✓ std3`).

*Citation.* Mihai-Silviu Lazorec and Marius Tărnăuceanu (2025). *On the number of conjugacy classes of subgroups of a finite group*. DOI: [10.48550/arXiv.2508.14267](https://doi.org/10.48550/arXiv.2508.14267). URL: <https://arxiv.org/html/2508.14267v2>.

*Commentary.*

FiniteGroup packages an actual carrier, its group operation, and a proof of finiteness. The displayed proposition is Problem 4.1 in https://arxiv.org/html/2508.14267v2, in integer cross-multiplied form. It quantifies over every pair of integers with 1 ≤ a < b. The witness has no nilpotence, supersolvability, coprimality or supplied counting-formula assumption. This declaration defines the exact target; it does not prove its attainment.

**Theorem 1.3 (Coprime product multiplicativity).**

$$\forall G \in Typeu,\; \forall K \in Typev,\; Group\left(G\right) \to \left(Group\left(K\right) \to \left(Finite\left(G\right) \to \left(Finite\left(K\right) \to \left(Coprime\left(card\left(G\right), card\left(K\right)\right) \to latticeCount\left(product\left(G, K\right)\right)=latticeCount\left(G\right)*latticeCount\left(K\right)\land classCount\left(product\left(G, K\right)\right)=classCount\left(G\right)*classCount\left(K\right)\land ratio\left(product\left(G, K\right)\right)=ratio\left(G\right)*ratio\left(K\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SubgroupConjugacyRatio.coprime_product_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mihai-Silviu Lazorec and Marius Tărnăuceanu (2025). *On the number of conjugacy classes of subgroups of a finite group*. DOI: [10.48550/arXiv.2508.14267](https://doi.org/10.48550/arXiv.2508.14267). URL: <https://arxiv.org/html/2508.14267v2>.

*Commentary.*

Let G and K be arbitrary finite groups whose orders are coprime. For every subgroup H of G × K and every (g,k) in H, taking powers first kills one component and then recovers the other using coprimality of its element order. Hence (g,1) and (1,k) belong to H. Conversely these two elements multiply to (g,k). Every subgroup is therefore exactly the product of its two projections.

subgroupProductEquiv sends H to its projected subgroups, with inverse their direct product. Conjugation by (g,k) acts separately on the two factors. Products of subgroups are conjugate exactly when their corresponding factors are conjugate. classesProductEquiv consequently identifies the quotient of the full product lattice with the product of the two full subgroup-conjugacy quotients. Cardinalities of these bijections give both count identities, and rational division gives the third identity. The ratio identity is already stated in Section 1 of Lazorec and Tărnăuceanu; the displayed conjunction records the two separate count identities as well as that known consequence. No multiplicativity statement for noncoprime orders is asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/SubgroupConjugacyRatio.RationalAttainment`
- Truth anchor: `D5/S3/FiniteGroups/SubgroupConjugacyRatio.coprime_product_counts`
- Truth anchor: `D5/S3/FiniteGroups/SubgroupConjugacyRatio.ratio`
