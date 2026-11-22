# Tărnăuceanu's rational normality-degree conjecture

## Abstract

Every rational in (0, 1] is the normality degree of a finite group.

**Definition 1.1 (Normal subgroups).**

$$\forall G \in Type,\; [Group\left(G\right)] NormalSubgroups\left(G\right) = \{H : Subgroup\left(G\right) \mid H.Normal\}$$

*Formalization.* `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.NormalSubgroups` (`✓ std3`).

*Citation.* Marius Tărnăuceanu (2017). *Normality degrees of finite groups*. DOI: [10.37193/CJM.2017.01.12](https://doi.org/10.37193/CJM.2017.01.12). URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf>.

*Commentary.*

The subtype consists of all subgroups H whose normality predicate holds. It contains both the trivial subgroup and the whole group, counted once when they coincide.

**Definition 1.2 (Normality degree).**

$$\forall G \in Type,\; [Group\left(G\right)] [Finite\left(G\right)] ndeg\left(G\right) = \frac{\operatorname{Nat.card}\left(NormalSubgroups\left(G\right)\right)}{latticeCount\left(G\right)}$$

*Formalization.* `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.ndeg` (`✓ std3`).

*Citation.* Marius Tărnăuceanu (2017). *Normality degrees of finite groups*. DOI: [10.37193/CJM.2017.01.12](https://doi.org/10.37193/CJM.2017.01.12). URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf>.

*Commentary.*

The denominator latticeCount G is Nat.card (Subgroup G), the cardinality of the full subgroup lattice. Both cardinalities are cast to the rationals.

**Definition 1.3 (Conjecture 4.1).**

$$\forall x \in \mathbb{Q},\; 0<x \Rightarrow \left(x\le1 \Rightarrow \left(\exists G \in Type,\; \exists group \in Group\left(G\right),\; \exists finite \in Finite\left(G\right),\; ndeg\left(G, group, finite\right) = x\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.claim` (`✓ std3`).

*Citation.* Marius Tărnăuceanu (2017). *Normality degrees of finite groups*. DOI: [10.37193/CJM.2017.01.12](https://doi.org/10.37193/CJM.2017.01.12). URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf>.

*Commentary.*

Conjecture 4.1 of the journal article, numbered Conjecture 4.4 in the preprint, asks for every rational x with 0 < x ≤ 1 an actual finite group of degree x. The existential witnesses supply the carrier, its group operation and laws, and a proof of finiteness.

**Theorem 1.4 (Exact rational attainment).**

$$\forall x \in \mathbb{Q},\; 0<x \Rightarrow \left(x\le1 \Rightarrow \left(\exists G \in Type,\; \exists group \in Group\left(G\right),\; \exists finite \in Finite\left(G\right),\; ndeg\left(G, group, finite\right) = x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marius Tărnăuceanu (2017). *Normality degrees of finite groups*. DOI: [10.37193/CJM.2017.01.12](https://doi.org/10.37193/CJM.2017.01.12). URL: <https://www.math.uaic.ro/~martar/pdf/articole/articol%2040.pdf>.

*Commentary.*

For x = 1, use the cyclic group of order two. In a commutative group every subgroup is normal, so the two cardinalities agree and are positive.

For 0 < x < 1, write x = u/v with 0 < u < v. Put d = v − u and t = 2d. Choose a prime p > 2t congruent to 1 modulo 2^t, and put B = pu + d − 1. Then t ≤ B. A unit modulo p of order 2^t gives an automorphism of the prime cyclic group of the same order. Sending the generator of the cyclic group of order 2^B to that automorphism forms the action of the semidirect product.

At every quotient level j = 0 through B, the subgroup containing the prime kernel is the inverse image of the level. It is normal. For j ≤ B − t, the action on the level is trivial and the standard section is the unique subgroup at that level meeting the kernel trivially. It is normal. For j > B − t, exactly p conjugate sections meet the kernel trivially. The generator acts without nonidentity fixed points on the prime kernel, so distinct kernel elements give distinct sections and conjugation by the kernel moves each section.

The resulting counts on the same group are 2B − t + 2 normal subgroups and 2B − t + 2 + pt subgroups in total. The counts agree with the specialization of the published ZM formula. Substituting B and t gives 2pu and 2pv, so their ratio is exactly u/v.

## References

- Truth anchor: `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.NormalSubgroups`
- Truth anchor: `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.claim`
- Truth anchor: `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.ndeg`
- Truth anchor: `D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization.result`
- Dependency: [D5/S3/FiniteGroups/CyclicPrimePowerAction](../CyclicPrimePowerAction.md)
