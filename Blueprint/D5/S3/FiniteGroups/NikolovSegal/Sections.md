# Sections of Arbitrary Subgroups

## Abstract

A group section is a surjective image of an arbitrary subgroup; simple sections split across a homomorphism and its kernel.

**Definition 1.1 (Arbitrary subgroup sections).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Involves\left(A, G\right) \Leftrightarrow \left(\exists H \in Subgroup\left(G\right),\; \exists f \in Hom\left(H, A\right),\; Surjective\left(f\right)\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/Sections.Involves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Involves(A,G) means that some arbitrary subgroup H of G admits a surjective group homomorphism to A. H need not be normal, and the map need not be defined on all of G. Hom(H,A) denotes the type of group homomorphisms.

**Lemma 1.2 (A surjective image is a section).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall f \in Hom\left(G, A\right),\; Surjective\left(f\right) \Rightarrow Involves\left(A, G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the whole group as the section subgroup. This auxiliary statement is used in the kernel branch of the simple-section dichotomy and to prove that the set of alternating degrees is nonempty.

**Lemma 1.3 (Sections pass through embeddings).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall Q \in Typew,\; Group\left(Q\right) \Rightarrow \left(\forall i \in Hom\left(G, Q\right),\; \left(Injective\left(i\right) \land Involves\left(A, G\right)\right) \Rightarrow Involves\left(A, Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective homomorphism carries the section subgroup to its image. Transport its surjection along the induced subgroup isomorphism; this also carries the Sylow-normalizer kernel section to its containing normalizer.

**Theorem 1.4 (A simple section occurs in the image or kernel).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall Q \in Typew,\; Group\left(Q\right) \Rightarrow \left(Simple\left(A\right) \Rightarrow \left(\forall q \in Hom\left(G, Q\right),\; Involves\left(A, G\right) \Rightarrow \left(Involves\left(A, Q\right) \lor Involves\left(A, ker\left(q\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.simple_involves_map_or_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a section map from H to a simple group A, the image of the kernel intersection is normal in A. If that image is trivial, the section map descends to the image of H in Q. If it is all of A, the kernel intersection surjects onto A and embeds in the ambient kernel. The homomorphism to Q is arbitrary and need not be surjective.

**Lemma 1.5 (Section order divides ambient order).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\left(Finite\left(G\right) \land Involves\left(A, G\right)\right) \Rightarrow card\left(A\right) \mid card\left(G\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_card_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite G, surjectivity makes the section order divide the subgroup order, and the subgroup order divides the ambient order. The symbol card denotes Nat.card.

**Lemma 1.6 (A divisibility obstruction to sections).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(Finite\left(G\right) \Rightarrow \left(\forall p \in Nat,\; \left(p \mid card\left(A\right) \land \left(\neg p \mid card\left(G\right)\right)\right) \Rightarrow \left(\neg Involves\left(A, G\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_of_prime_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any natural number p dividing the proposed section order but not the finite ambient order excludes that section. Despite the declaration name, this statement does not require p to be prime.

**Lemma 1.7 (Sections of a p-group are p-groups).**

$$\forall A \in Typeu,\; Group\left(A\right) \Rightarrow \left(\forall G \in Typev,\; Group\left(G\right) \Rightarrow \left(\forall p \in Nat,\; \left(IsPGroup\left(p, G\right) \land \left(\neg IsPGroup\left(p, A\right)\right)\right) \Rightarrow \left(\neg Involves\left(A, G\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_pGroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subgroups and surjective images preserve the p-group property. There is no finiteness or primality hypothesis in this auxiliary obstruction.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.Involves`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_card_dvd`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_injective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_surjective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_of_prime_dvd`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_pGroup`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/Sections.simple_involves_map_or_kernel`
