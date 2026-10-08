# Elementary minimal normal structure

## Abstract

A nonabelian minimal nontrivial normal subgroup of a finite ambient group is perfect and centerless, and its canonical internal product of actual minimal normal factors is isomorphic to it.

**Lemma 1.1 (Characteristic subgroups are trivial or full).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.characteristic_subgroup_of_minimal_normal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.characteristic_subgroup_of_minimal_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G and minimal nontrivial normal subgroup N, every characteristic subgroup K of N is bottom or top. Its image in G is normal, and minimal normality of N applies. No finiteness or nonabelian hypothesis is required.

**Lemma 1.2 (Nonabelian minimal normal subgroups are perfect and centerless).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.perfect_centerless_minimal_normal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.perfect_centerless_minimal_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G and nonabelian minimal nontrivial normal subgroup N, the commutator subgroup of N is top and its center is bottom. Both are characteristic; their opposite possibilities would make N commutative.

**Lemma 1.3 (The finite minimal normal subgroup has full socle).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socle_of_finite_minimal_normal`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socle_of_finite_minimal_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ambient group G and minimal nontrivial normal subgroup N, the socle of N is top, including when N is abelian. A finite nontrivial group has a minimal nontrivial normal subgroup, so the characteristic socle cannot be bottom.

**Definition 1.4 (The canonical internal product is an isomorphism).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socleProductEquiv`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socleProductEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite group G with full socle and bottom center, socleProductEquiv maps the product of its actual minimal normal factors isomorphically onto G. The index family and each factor are finite. The canonical product homomorphism is surjective by the full socle and injective by full supremum independence.

**Theorem 1.5 (The elementary nonabelian decomposition).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.minimal_normal_nonabelian_direct_product`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.minimal_normal_nonabelian_direct_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ambient group G and nonabelian minimal nontrivial normal subgroup N, N is perfect and centerless, every actual minimal normal factor of N is nonabelian simple, and the internal product of these factors is isomorphic to N. The proof uses characteristic subgroups, the socle and internal products; no classification of finite simple groups or power bound is assumed.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.characteristic_subgroup_of_minimal_normal`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.minimal_normal_nonabelian_direct_product`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.perfect_centerless_minimal_normal`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socleProductEquiv`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socle_of_finite_minimal_normal`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/FiniteNormalInduction](FiniteNormalInduction.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle](MinimalNormalSocle.md)
