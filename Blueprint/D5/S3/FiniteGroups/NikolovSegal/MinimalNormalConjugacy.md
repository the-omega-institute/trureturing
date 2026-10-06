# Ambient conjugacy of the actual factors

## Abstract

Ambient conjugates of a nontrivial subgroup fill a minimal normal subgroup; ambient conjugation is transitive on its nonabelian simple factors.

**Lemma 1.1 (Ambient conjugates join to the whole subgroup).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.conjugate_join_of_minimal_normal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.conjugate_join_of_minimal_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G, normal minimal nontrivial subgroup N, and nontrivial subgroup M of N, the join of M mapped by the restrictions of conjugation by all g in G is top in N. The image of that join in G is normal and nontrivial, so minimal normality applies.

**Theorem 1.2 (Ambient conjugation is transitive on factors).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite group G and normal minimal nontrivial subgroup N that is nonabelian, any two actual minimal normal factors of N are conjugate by an element of G. If all conjugates of one factor differed from the other, their full join would centralize the other, contradicting centerlessness.

**Lemma 1.3 (All factors are isomorphic).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_isomorphic`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_isomorphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same finite ambient group, minimal normality and nonabelian hypotheses, any two actual factors are isomorphic via ambient conjugation. Their orders therefore agree.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.conjugate_join_of_minimal_normal`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_conjugate`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_isomorphic`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure](MinimalNormalStructure.md)
