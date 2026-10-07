# Closure of the bounded-section class

## Abstract

For finite groups, a bound on every alternating section passes through subgroups and quotients and is stable under extensions when the threshold is at least four.

**Lemma 1.1 (Sections lift through a surjection).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.involves_of_surjective_image`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.involves_of_surjective_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary groups G, Q and A and a surjective homomorphism q from G to Q, Involves(A,Q) implies Involves(A,G). Pull back the section subgroup and compose its surjection to A. The section subgroup need not be normal.

**Lemma 1.2 (The maximum controls every section).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_iff_sections`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_iff_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite group G and natural k, alpha(G) is at most k if and only if every natural n for which the alternating group on Fin n is a section of G satisfies n at most k. This uses the genuine maximum alpha_spec, including small alternating degrees.

**Lemma 1.3 (Trivial groups satisfy the small bound).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_four_of_subsingleton`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_four_of_subsingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite subsingleton group has alpha at most four. Its order is one, and the alternating-degree cardinality bound excludes larger sections.

**Lemma 1.4 (Bounds pass through faithful maps).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite groups G and Q and an injective homomorphism from G to Q, alpha(G) is at most alpha(Q). An arbitrary subgroup section of G transports to a subgroup section of Q.

**Lemma 1.5 (Bounds pass through subgroup inclusions).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_subgroup_le`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_subgroup_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For subgroups H and K of a finite group G, H contained in K implies alpha(H) at most alpha(K). Apply the injective-map bound to the inclusion homomorphism.

**Lemma 1.6 (Bounds pass to quotient images).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite groups G and Q and a surjective homomorphism from G to Q, alpha(Q) is at most alpha(G). Pull back each alternating section of Q.

**Lemma 1.7 (Kernel and codomain bounds give an extension bound).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_kernel_codomain`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_kernel_codomain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite groups G and Q, any homomorphism q from G to Q, and any natural k at least four, alpha(ker q) at most k and alpha(Q) at most k imply alpha(G) at most k. Surjectivity is unnecessary. Alternating groups in degrees at least five are simple, so their sections occur in Q or ker q; smaller degrees are already bounded by k.

**Lemma 1.8 (Normal extensions remain bounded).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_normal_extension`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_normal_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite group G, normal subgroup N and natural k at least four, alpha(N) at most k and alpha(G/N) at most k imply alpha(G) at most k. Use the quotient homomorphism and its kernel.

**Lemma 1.9 (The first isomorphism bounds a quotient).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_quotient_kernel_le`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_quotient_kernel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite groups G and Q and any homomorphism q from G to Q, alpha(G/ker q) is at most alpha(Q). The first-isomorphism embedding is faithful, even when q is not surjective.

**Lemma 1.10 (Preimages of bounded subgroups).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_preimage_le`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_preimage_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite groups G and Q, any homomorphism q from G to Q, any subgroup H of Q, and natural k at least four, bounds alpha(ker q) at most k and alpha(H) at most k imply alpha(q inverse image of H) at most k. Restrict q to this preimage; its kernel embeds into ker q.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_four_of_subsingleton`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_iff_sections`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_injective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_kernel_codomain`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_normal_extension`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_subgroup_le`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_le_of_surjective`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_preimage_le`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.alpha_quotient_kernel_le`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/SectionClosure.involves_of_surjective_image`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2](NikolovSegalLemma2.md)
