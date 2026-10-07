# Nikolov-Segal Lemma 2: Supplements and Alternating Sections

## Abstract

Every normal subgroup of a finite group has a supplement controlling all alternating sections of degree at least five and the largest alternating section degree.

**Theorem 1.1 (Sections descend through the quotient).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\left(Finite\left(G\right) \land Simple\left(A\right)\right) \Rightarrow \left(\forall N \in Subgroup\left(G\right),\; Normal\left(N\right) \Rightarrow \left(\forall p \in Nat,\; Prime\left(p\right) \Rightarrow \left(\forall P \in Sylow\left(p, N\right),\; \left(\left(\left(\neg IsPGroup\left(p, A\right)\right) \land p \mid card\left(A\right)\right) \land Involves\left(A, normalizer\left(image\left(P, inclusion\left(N\right)\right)\right)\right)\right) \Rightarrow Involves\left(A, Quotient\left(G, N\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.sylow_normalizer_section_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Sylow p-subgroup P of N, take the normalizer in G of its image under the inclusion of N in G. The kernel of the restricted quotient map embeds in the normalizer of P inside N. The simple-section dichotomy and the Sylow-normalizer obstruction therefore force every indicated section into G/N. The image and normalizer refer to the subgroup inclusion, not a change of section definition.

**Theorem 1.2 (One supplement transfers every large alternating section).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow \left(\forall N \in Subgroup\left(G\right),\; Normal\left(N\right) \Rightarrow \left(\exists L \in Subgroup\left(G\right),\; join\left(N, L\right) = top \land \left(\forall k \in Nat,\; \left(5 \le k \land Involves\left(alternatingGroup\left(Fin\left(k\right)\right), L\right)\right) \Rightarrow Involves\left(alternatingGroup\left(Fin\left(k\right)\right), Quotient\left(G, N\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_preserving_alternating_sections` (`✓ std3`). ∎

*Citation.* Nikolay Nikolov and Dan Segal (2011). *Powers in finite groups*. DOI: [10.4171/GGD/136](https://doi.org/10.4171/GGD/136). URL: <https://doi.org/10.4171/GGD/136>.

*Commentary.*

Choose a Sylow 2-subgroup P of N and let L be the normalizer in G of its image. Frattini gives N join L equal to G. For every k at least five, Alt(k) is simple, has even order, and is not a 2-group, so its sections in L descend to G/N. The existential quantifier for L precedes the universal quantifier for k: the same supplement works for all such degrees.

**Theorem 1.3 (The exact largest-degree inequality).**

$$\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow \left(\forall N \in Subgroup\left(G\right),\; Normal\left(N\right) \Rightarrow \left(\exists L \in Subgroup\left(G\right),\; join\left(N, L\right) = top \land alpha\left(L\right) \le max\left(alpha\left(Quotient\left(G, N\right)\right), 4\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_alpha_le` (`✓ std3`). ∎

*Citation.* Nikolay Nikolov and Dan Segal (2011). *Powers in finite groups*. DOI: [10.4171/GGD/136](https://doi.org/10.4171/GGD/136). URL: <https://doi.org/10.4171/GGD/136>.

*Commentary.*

This is Powers in finite groups, printed page 504, Lemma 2. Use the same Sylow-normalizer supplement as in the section-transfer theorem and apply the attained maximum characterization of alpha. All finite groups and all normal subgroups are allowed, including the bottom and top normal subgroups. This structural lemma does not by itself establish the power-width, restricted Burnside, or profinite strong-completeness targets.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_alpha_le`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_preserving_alternating_sections`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.sylow_normalizer_section_transfer`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Alpha](Alpha.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/AlternatingBounds](AlternatingBounds.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/SylowKernel](SylowKernel.md)
