# Graph-wide degree and gap compensation

## Abstract

Graph-wide degree and gap compensation

The actual augmented exchanges combine with the checked finite degree-capacity sum. The degree-weighted inequality applies to every finite bipartite graph with a maximum degree bound; minimum and maximum degrees give the displayed SF bound. Actual finite attainment then yields (2d+1)SF<=dn+2 beta for regular bipartite graphs. For positive d the canonical gap is at most floor(n/(4d+2)). The exact augmented regular remainder identity is proved; no equality partition or extremal construction is inferred from its algebra alone.

**Theorem 1.1 (weighted selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.weighted_selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.weighted_selection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem weighted_selection_bound (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, DegreeCapacity.degree G v ≤ D) : (∑ v ∈ S, DegreeCapacity.degree G v) + (D + 1) * S.card ≤ D * Fintype.card V + 2 * beta G 2.

**Theorem 1.2 (min max selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.min_max_selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.min_max_selection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem min_max_selection_bound (hG : G.Colorable 2) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (delta D : ℕ) (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v) (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) : (delta + D + 1) * S.card ≤ D * Fintype.card V + 2 * beta G 2.

**Theorem 1.3 (sf min max bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_min_max_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_min_max_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_min_max_bound (hG : G.Colorable 2) (delta D : ℕ) (hmin : ∀ v, delta ≤ DegreeCapacity.degree G v) (hmax : ∀ v, DegreeCapacity.degree G v ≤ D) : (delta + D + 1) * SF G 2 ≤ D * Fintype.card V + 2 * beta G 2.

**Theorem 1.4 (sf regular bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_regular_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_regular_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_regular_bound (hG : G.Colorable 2) (d : ℕ) (hregular : ∀ v, DegreeCapacity.degree G v = d) : (2 * d + 1) * SF G 2 ≤ d * Fintype.card V + 2 * beta G 2.

**Theorem 1.5 (sf sub beta bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_sub_beta_bound (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : (4 * d + 2) * (SF G 2 - beta G 2) ≤ Fintype.card V.

**Theorem 1.6 (sf sub beta floor).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_sub_beta_floor (hG : G.Colorable 2) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : SF G 2 - beta G 2 ≤ Fintype.card V / (4 * d + 2).

**Theorem 1.7 (regular remainder).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.regular_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.regular_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem regular_remainder (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) : (d : ℤ) * Fintype.card V + 2 * beta G 2 - (2 * d + 1) * S.card = ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color false).card) + ((beta G 2 : ℤ) - (BipartiteExchange.exchange G S hS color true).card) + ((d : ℤ) * Fintype.card V - (2 * d - 1) * S.card - (DegreeCapacity.isolates G S).card).

**Theorem 1.8 (linear equality iff).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.linear_equality_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.linear_equality_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem linear_equality_iff (color : V → Bool) (hcolor : ∀ v w, G.Adj v w → color v ≠ color w) (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, DegreeCapacity.degree G v = d) : d * Fintype.card V + 2 * beta G 2 = (2 * d + 1) * S.card ↔ ((2 * d - 1) * S.card + (DegreeCapacity.isolates G S).card = d * Fintype.card V) ∧ (BipartiteExchange.exchange G S hS color false).card = beta G 2 ∧ (BipartiteExchange.exchange G S hS color true).card = beta G 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.linear_equality_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.min_max_selection_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.regular_remainder`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_min_max_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_regular_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.sf_sub_beta_floor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/RegularCompensation.weighted_selection_bound`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/BipartiteExchange](BipartiteExchange.md)
