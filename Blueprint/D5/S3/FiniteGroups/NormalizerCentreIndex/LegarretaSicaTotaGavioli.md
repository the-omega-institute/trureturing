# Normalizer counts and centre index

## Abstract

The centre index is unbounded while the number of normalizer classes stays eight.

**Definition 1.1 (The general-group question).**

$$claim = \left(\exists B \in \mathbb{N} \to \mathbb{N},\; \forall G \in Type,\; [Group\left(G\right)] (\forall H \in Subgroup\left(G\right),\; (H\neq \operatorname{Top}.\operatorname{top}) \Rightarrow (H<\operatorname{Subgroup}.\operatorname{normalizer}\left((H: Set\left(G\right))\right))) \Rightarrow ((Finite\left(NormalizerClass\left(G\right)\right)) \Rightarrow ((((omega\left(G\right): \mathbb{N}): Cardinal)<sCard\left(G\right)) \Rightarrow (centreIndex\left(G\right)\le ((B\left(omega\left(G\right)\right): \mathbb{N}): Cardinal))))\right)$$

*Formalization.* `D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.claim` (`✓ std3`).

*Citation.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

Question 3.3. Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups? Printed page 1174. “NC: every proper subgroup H of G is properly contained in its normalizer N_G(H).” Printed page 1169. The target is the first question. The function B maps natural numbers to natural numbers. NormalizerWitness counts distinct normalizer subgroups, including the whole group; NormalizerClass identifies them by inner conjugacy. The centre index and the number of normalizers are cardinal-valued. The cardinal comparison retains infinite indices. omega is Nat.card of the quotient, used with its explicit finiteness hypothesis.

**Theorem 1.2 (A family with fixed normalizer counts).**

$$\neg (\exists B \in \mathbb{N} \to \mathbb{N},\; \forall G \in Type,\; [Group\left(G\right)] (\forall H \in Subgroup\left(G\right),\; (H\neq \operatorname{Top}.\operatorname{top}) \Rightarrow (H<\operatorname{Subgroup}.\operatorname{normalizer}\left((H: Set\left(G\right))\right))) \Rightarrow ((Finite\left(NormalizerClass\left(G\right)\right)) \Rightarrow ((((omega\left(G\right): \mathbb{N}): Cardinal)<sCard\left(G\right)) \Rightarrow (centreIndex\left(G\right)\le ((B\left(omega\left(G\right)\right): \mathbb{N}): Cardinal)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Leire Legarreta, Carmela Sica, Maria Tota and Norberto Gavioli (2010). *On the Number of Normalizers and Conjugacy Classes of Normalizers*. URL: <https://www.m-hikari.com/ija/ija-2010/ija-21-24-2010/totaIJA21-24-2010.pdf>.

*Commentary.*

For each odd prime p, take the product of the group of order sixteen with presentation a⁸ = b² = 1, b⁻¹ab = a³, and the modular group of order p³ with action yxy⁻¹ = x¹⁺ᵖ. The first factor has five normalizers and four conjugacy classes of normalizers. The modular factor has two of each. Coprimality splits subgroups and normalizers coordinatewise. The product has ten normalizers, eight classes, and centre index 8p². It is finite nilpotent, so every proper subgroup is strictly contained in its normalizer. Unbounded odd primes contradict any natural bound at eight. The separate finite-p-group question is left open.

## References

- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.claim`
- Truth anchor: `D5/S3/FiniteGroups/NormalizerCentreIndex/LegarretaSicaTotaGavioli.result`
- Dependency: [D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors](ModularNormalizerFactors.md)
