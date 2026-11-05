# Double-hub incidence

## Abstract

The physical double-hub family: incidence.

Incidence degree agrees with degree in the actual graph. An automorphism fixes the centre, permutes the two hubs, and independently permutes the m leaves of each hub. Conversely every such triple gives an automorphism. This gives the exact order 2(m!)^2, including the five-vertex path at m=1.

The five two-edge placement classes have cardinalities 1,2m,2m,m(m-1),m^2. The same-hub pendant class is empty at m=1; no stabilizer is assigned to an empty class. Direct finite sums over the classes retain every placement.

The source prefactor is 4/(9 times the automorphism order). The physical factorial factor is 16200(m!)^2 times 12^(2m) times the endpoint ratios. After the normalized endpoint block is evaluated, the common coefficient scalar is exactly 200 times 12^(2m). No extra factorial for a formal generator is introduced.

These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.

**Theorem 1.1 (incidence degree).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.incidence_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.incidence_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constructs neighbourhood/incidence correspondence for this actual graph. Exact source statement: theorem incidence_degree (m : ℕ) (v : Vertex m) :     degree v = (graph m).degree v.

**Theorem 1.2 (actual automorphism order).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_automorphism_order`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_automorphism_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classifies actual graph automorphisms via hub and independent leaf permutations and derives their order. Exact source statement: theorem actual_automorphism_order (m : ℕ) (hm : 1 ≤ m) :     automorphismOrder m = 2*(Nat.factorial m)^2.

**Theorem 1.3 (actual zero coupling boundaries).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_zero_coupling_boundaries`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_zero_coupling_boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transfers actual weighted-source positivity and coupling symmetry to both axes and the origin. Exact source statement: theorem actual_zero_coupling_boundaries (m cutoff : ℕ)     (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :     (∀ a : ℂ, a ≠ 0 → homogeneousCoefficient m cutoff a 0 ≠ 0) ∧     (∀ b : ℂ, b ≠ 0 → homogeneousCoefficient m cutoff 0 b ≠ 0) ∧     homogeneousCoefficient m cutoff 0 0 = 0.

**Theorem 1.4 (actual source normalization).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_source_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_source_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_source_normalization (m cutoff : ℕ)     (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :     sourceCoefficient m cutoff = Polynomial.C (200*(12:ℝ)^(2*m)) *       ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,         ∑ S ∈ A.powerset,           Polynomial.C (18 * ∏ v : Vertex m, endpointRatio (degree v) (increments A S v)) *             ∏ v : Vertex m, (1 + Polynomial.C ((-1:ℝ)^degree v) *               Polynomial.X^(degree v+increments A S v)).

**Definition 1.5 (placementsCC).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCC`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCC` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines placementsCC for the physical double-hub family.

**Definition 1.6 (placementsCPsame).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPsame`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPsame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines placementsCPsame for the physical double-hub family.

**Definition 1.7 (placementsCPopp).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPopp`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPopp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines placementsCPopp for the physical double-hub family.

**Definition 1.8 (placementsPPsame).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPsame`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPsame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines placementsPPsame for the physical double-hub family.

**Definition 1.9 (placementsPPopp).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPopp`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPopp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines placementsPPopp for the physical double-hub family.

**Theorem 1.10 (placement exhaustive).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_exhaustive`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Classifies every actual two-edge subset in one of the five geometric classes. Exact source statement: theorem placement_exhaustive (m : ℕ) (A : Finset (Edge m)) (hA : A.card = 2) :     A ∈ placementsCC m ∨ A ∈ placementsCPsame m ∨ A ∈ placementsCPopp m ∨       A ∈ placementsPPsame m ∨ A ∈ placementsPPopp m.

**Theorem 1.11 (placement counts).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_counts`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counts all five actual finite classes uniformly in m, including an empty same-branch class at m=1. Exact source statement: theorem placement_counts (m : ℕ) :     (placementsCC m).card = 1 ∧     (placementsCPsame m).card = 2*m ∧     (placementsCPopp m).card = 2*m ∧     (placementsPPsame m).card = m*(m-1) ∧     (placementsPPopp m).card = m^2.

**Definition 1.12 (selectedLeaves).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.selectedLeaves`

*Formalization.* `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.selectedLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This defines selectedLeaves for the physical double-hub family.

**Theorem 1.13 (leaf vertex product).**

Lean statement: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.leaf_vertex_product`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.leaf_vertex_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem leaf_vertex_product (m : ℕ) (A S : Finset (Edge m)) :     (∏ bi : Bool × Fin m,       Polynomial.C (endpointRatio (degree (some (bi.1,some bi.2)))         (increments A S (some (bi.1,some bi.2)))) *       (1+Polynomial.C ((-1:ℝ)^degree (some (bi.1,some bi.2))) *         Polynomial.X^(degree (some (bi.1,some bi.2))+           increments A S (some (bi.1,some bi.2))))) =     (1-Polynomial.X)^(2*m) *       (Polynomial.C (1/3:ℝ)*(1+Polynomial.X))^(selectedLeaves m S).card.

## References

- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_automorphism_order`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_source_normalization`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.actual_zero_coupling_boundaries`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.incidence_degree`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.leaf_vertex_product`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_counts`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placement_exhaustive`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCC`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPopp`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsCPsame`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPopp`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.placementsPPsame`
- Truth anchor: `D5/S3/Zeros/LeeYang/FiolDoubleHubIncidence.selectedLeaves`
- Dependency: [D5/S3/Zeros/LeeYang/FiolDoubleHubGrid](FiolDoubleHubGrid.md)
- Dependency: [D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation](QuiverTreeIsingRefutation.md)
