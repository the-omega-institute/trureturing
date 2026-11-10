# Global finite degree capacity

## Abstract

Global finite degree capacity

For every finite simple graph and every minimal two-star-forming S, the sum of ambient degrees on S plus the number of selected isolates is at most |S| plus Delta times the outside cardinality. This is the integer sum(deg-1)+z form without natural-number truncation. The chosen high-vertex failure map is injective, the actual outside capacity is summed only once, and the cut is counted on both sides. For d-regular graphs with d at least one, (2d-1)|S|+z<=d|V|, hence SF two<=floor(d|V|/(2d-1)). No equality classification, extremal construction or sharp compensation theorem is inferred from this upper bound alone.

**Definition 1.1 (degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def degree (v : V) : ℕ.

**Definition 1.2 (selectedDegree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selectedDegree`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selectedDegree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def selectedDegree (S : Finset V) (v : V) : ℕ.

**Definition 1.3 (isolates).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.isolates`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.isolates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact declaration: def isolates (S : Finset V) : Finset V.

**Theorem 1.4 (failure selected degree le two).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.failure_selected_degree_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.failure_selected_degree_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem failure_selected_degree_le_two (S : Finset V) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) : selectedDegree G S x ≤ 2.

**Theorem 1.5 (adjacent failure degree).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.adjacent_failure_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.adjacent_failure_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem adjacent_failure_degree (S : Finset V) (D : ℕ) (hD : ∀ v, degree G v ≤ D) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) (hedge : G.Adj x v) : selectedDegree G S v + 1 ≤ D.

**Theorem 1.6 (witness degree capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.witness_degree_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.witness_degree_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem witness_degree_capacity (S : Finset V) (D : ℕ) (hD : ∀ v, degree G v ≤ D) (v x : V) (hx : Regular.Failure G.Adj (· ∈ S) v x) : selectedDegree G S v + selectedDegree G S x ≤ D + 1.

**Theorem 1.7 (high capacity sum).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.high_capacity_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.high_capacity_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem high_capacity_sum (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, degree G v ≤ D) : ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1) ≤ ∑ x ∈ Finset.univ \ S, (D - selectedDegree G S x).

**Theorem 1.8 (degree sum cut).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_sum_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_sum_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem degree_sum_cut (S : Finset V) : ∑ v ∈ S, degree G v = (∑ v ∈ S, selectedDegree G S v) + ∑ x ∈ Finset.univ \ S, selectedDegree G S x.

**Theorem 1.9 (selected degree identity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selected_degree_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selected_degree_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem selected_degree_identity (S : Finset V) : (∑ v ∈ S, selectedDegree G S v) + (isolates G S).card = S.card + ∑ v ∈ CertificateBound.high G S, (selectedDegree G S v - 1).

**Theorem 1.10 (degree capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem degree_capacity (S : Finset V) (hS : IsMinimalStarForming G 2 S) (D : ℕ) (hD : ∀ v, degree G v ≤ D) : (∑ v ∈ S, degree G v) + (isolates G S).card ≤ S.card + D * (Finset.univ \ S).card.

**Theorem 1.11 (regular selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.regular_selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.regular_selection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem regular_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S) (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) : (2 * d - 1) * S.card + (isolates G S).card ≤ d * Fintype.card V.

**Theorem 1.12 (sf regular bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_regular_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_regular_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_regular_bound (d : ℕ) (hd : 1 ≤ d) (hregular : ∀ v, degree G v = d) : SF G 2 ≤ d * Fintype.card V / (2 * d - 1).

**Theorem 1.13 (min max selection bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.min_max_selection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.min_max_selection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem min_max_selection_bound (S : Finset V) (hS : IsMinimalStarForming G 2 S) (delta D : ℕ) (hpositive : 2 ≤ delta + D) (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) : (delta + D - 1) * S.card + (isolates G S).card ≤ D * Fintype.card V.

**Theorem 1.14 (sf min max bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_min_max_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_min_max_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem sf_min_max_bound (delta D : ℕ) (hpositive : 2 ≤ delta + D) (hmin : ∀ v, delta ≤ degree G v) (hmax : ∀ v, degree G v ≤ D) : SF G 2 ≤ D * Fintype.card V / (delta + D - 1).

**Theorem 1.15 (dissociation cut bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_cut_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_cut_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem dissociation_cut_bound (S : Finset V) (hS : IsKIndependent G 2 S) : 2 * (∑ v ∈ S, degree G v) ≤ S.card + ∑ v : V, degree G v.

**Theorem 1.16 (dissociation deficiency bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_deficiency_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_deficiency_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact declaration: theorem dissociation_deficiency_bound (S : Finset V) (hS : IsKIndependent G 2 S) (d : ℕ) (hd : 1 ≤ d) (hmax : ∀ v, degree G v ≤ d) : (2 * d - 1) * S.card + (∑ v : V, (d - degree G v)) ≤ d * Fintype.card V + 2 * (∑ v ∈ S, (d - degree G v)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.adjacent_failure_degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.degree_sum_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_cut_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.dissociation_deficiency_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.failure_selected_degree_le_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.high_capacity_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.isolates`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.min_max_selection_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.regular_selection_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selectedDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.selected_degree_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_min_max_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.sf_regular_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity.witness_degree_capacity`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CertificateBound](CertificateBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
