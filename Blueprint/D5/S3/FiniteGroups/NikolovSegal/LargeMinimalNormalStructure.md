# Large minimal normal subgroups

## Abstract

A fixed factorial cutoff and large alternating-section degree force every actual factor of a finite minimal normal subgroup to be nonabelian simple of order above the cutoff.

**Lemma 1.1 (Sections of commutative groups are commutative).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.commutative_section`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.commutative_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary groups G and A, if G is commutative and A is a section of G, then A is commutative. Lift any two elements through the section surjection and use commutativity in its arbitrary subgroup.

**Lemma 1.2 (Large alternating-section degree implies noncommutativity).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.noncommutative_of_large_alpha`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.noncommutative_of_large_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite group G and natural k with four at most k, alpha(G) greater than k implies G is noncommutative. A commutative alternating section has degree at most three, contradicting the bound. Here alpha is the largest degree of an alternating section formed from an arbitrary subgroup.

**Theorem 1.3 (Every factor exceeds the fixed cutoff).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_structure`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural C and k with four at most k and twice C less than k factorial, every finite ambient group G and minimal nontrivial normal subgroup N with alpha(N) greater than k satisfies: N is perfect and its center is bottom; every actual minimal normal factor of N is nonabelian simple and has order greater than C; their internal product is isomorphic to N. The actual factor family and factors are finite. An alternating section of degree alpha(N) occurs in one factor and bounds its order from below; ambient factor conjugacy transfers that bound to every factor. No decomposition or conjugacy premise is assumed.

**Theorem 1.4 (The central quotient has the required large simple factors).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_proposition2_data`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_proposition2_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same fixed C and k, finite ambient G, minimal nontrivial normal N and alpha(N) greater than k, N is perfect, every actual factor is nonabelian simple of order greater than C, and N modulo its center is isomorphic to the actual product of those factors. This supplies the elementary structural hypotheses preceding the coset-power theorem. Uniform prescribed-coset power surjectivity remains an additional unproved input; this conclusion gives no uniform absorption, power width or strong completeness theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.commutative_section`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_proposition2_data`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_structure`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.noncommutative_of_large_alpha`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/Alpha](Alpha.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy](MinimalNormalConjugacy.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/SimpleSectionsOfProducts](SimpleSectionsOfProducts.md)
