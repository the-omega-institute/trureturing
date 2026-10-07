# Minimal normal factors and the socle

## Abstract

Actual minimal normal subgroups form a characteristic socle. When that socle fills a centerless group, its factors are nonabelian simple and fully independent.

**Definition 1.1 (Actual minimal normal factors).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.MinimalNormalFactor`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.MinimalNormalFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any group G, MinimalNormalFactor G consists of subgroups M minimal for the predicate that M is normal and not the bottom subgroup. The factors are actual subgroups of G.

**Definition 1.2 (The socle is the join of the factors).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any group G, minimalNormalSocle G is the supremum of all its actual minimal nontrivial normal subgroups.

**Lemma 1.3 (Isomorphisms transport minimal normality).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_map_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_map_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary groups G and Q, an isomorphism e from G to Q maps a minimal nontrivial normal subgroup of G to one of Q. Pullback and pushforward preserve nontriviality and the complete minimality condition.

**Lemma 1.4 (The socle is characteristic).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle_characteristic`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle_characteristic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every automorphism permutes the actual minimal normal factors, so their join is characteristic. No finiteness assumption is needed.

**Lemma 1.5 (Distinct factors commute).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_commute`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In any group G, distinct minimal nontrivial normal subgroups intersect trivially. Their commutator subgroup lies in that intersection, so every element of one commutes with every element of the other.

**Lemma 1.6 (A full socle makes each factor simple).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.simple_minimal_normal_factor_of_socle_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.simple_minimal_normal_factor_of_socle_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the socle of any group G is the top subgroup, every actual minimal normal factor is simple. A subgroup normal within one factor is normalized by that factor and centralized by every other factor, hence normalized by the full socle. Minimal normality then makes it trivial or the entire factor.

**Lemma 1.7 (Centerlessness gives full independence).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_independent`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G with full socle and bottom center, each factor is disjoint from the join of all other factors. An element in the intersection commutes with every factor and hence belongs to the bottom center. This is full supremum independence, which is stronger than pairwise disjointness.

**Lemma 1.8 (Every factor is nonabelian).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.noncommutative_minimal_normal_factor_of_socle_eq_top`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.noncommutative_minimal_normal_factor_of_socle_eq_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any group G with full socle and bottom center, no minimal normal factor is commutative. A commutative factor would commute both with itself and with all other factors, placing it in the center and contradicting nontriviality.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.MinimalNormalFactor`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle_characteristic`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_commute`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_independent`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_map_equiv`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.noncommutative_minimal_normal_factor_of_socle_eq_top`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.simple_minimal_normal_factor_of_socle_eq_top`
