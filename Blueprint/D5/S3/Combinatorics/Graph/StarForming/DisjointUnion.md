# Finite disjoint unions and actual attainment

## Abstract

Finite disjoint unions and actual attainment

For finite simple graphs and every natural k, formation and inclusion-minimality hold exactly componentwise under the graph disjoint sum. This includes empty components and k zero; in particular it proves the positive-k statement of the received source. The actual canonical maxima beta and SF are each additive. Every maximum is attained by an actual finite selection; minimal forming selections exist even in graphs without any k-star.

**Theorem 1.1 (starForming sum left).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_left`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem starForming_sum_left (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) : IsStarForming G k S.toLeft.

**Theorem 1.2 (starForming sum right).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_right`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem starForming_sum_right (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) (h : IsStarForming (G ⊕g H) k S) : IsStarForming H k S.toRight.

**Theorem 1.3 (starForming sum iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem starForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) : IsStarForming (G ⊕g H) k S ↔ IsStarForming G k S.toLeft ∧ IsStarForming H k S.toRight.

**Theorem 1.4 (minimalStarForming sum iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_sum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem minimalStarForming_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) (S : Finset (V ⊕ W)) : IsMinimalStarForming (G ⊕g H) k S ↔ IsMinimalStarForming G k S.toLeft ∧ IsMinimalStarForming H k S.toRight.

**Theorem 1.5 (beta attained).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_attained (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ∃ S : Finset V, IsKIndependent G k S ∧ S.card = beta G k.

**Theorem 1.6 (minimalStarForming exists).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem minimalStarForming_exists (G : SimpleGraph V) (k : ℕ) : ∃ S : Finset V, IsMinimalStarForming G k S.

**Theorem 1.7 (sf attained).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_attained (G : SimpleGraph V) (k : ℕ) : ∃ S : Finset V, IsMinimalStarForming G k S ∧ S.card = SF G k.

**Theorem 1.8 (independent sum iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.independent_sum_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.independent_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem independent_sum_iff (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) (S : Finset (V ⊕ W)) : IsKIndependent (G ⊕g H) k S ↔ IsKIndependent G k S.toLeft ∧ IsKIndependent H k S.toRight.

**Theorem 1.9 (beta sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem beta_sum (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (k : ℕ) : beta (G ⊕g H) k = beta G k + beta H k.

**Theorem 1.10 (sf sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_sum (G : SimpleGraph V) (H : SimpleGraph W) (k : ℕ) : SF (G ⊕g H) k = SF G k + SF H k.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_attained`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.beta_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.independent_sum_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_exists`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.minimalStarForming_sum_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_attained`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.sf_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_left`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DisjointUnion.starForming_sum_right`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](../StarFormingDissociationRefutation.md)
