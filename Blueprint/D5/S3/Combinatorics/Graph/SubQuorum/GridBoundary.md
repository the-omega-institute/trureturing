# Actual grid boundary deficiency and forming bound

## Abstract

Actual grid boundary deficiency and forming bound

The actual Cartesian graph degree counts all four missing directions separately, including coincident endpoints in width-one paths. For positive dimensions total deficiency is exactly twice each dimension. The general degree-capacity theorem proves the selected-deficiency estimate seven times the selection size plus its actual isolates at most four times the order plus selected deficiency, and its perimeter consequence. No coloring or representative equality follows from this forming bound.

**Theorem 1.1 (degree formula).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_formula` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degree_formula {m n : ℕ} (v : Fin m × Fin n) : DegreeCapacity.degree (graph m n) v= (if v.1.val=0 then 0 else 1)+(if v.1.val+1=m then 0 else 1)+ (if v.2.val=0 then 0 else 1)+(if v.2.val+1=n then 0 else 1).

**Theorem 1.2 (degree le four).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_le_four` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem degree_le_four {m n : ℕ} (v : Fin m × Fin n) : DegreeCapacity.degree (graph m n) v≤4.

**Theorem 1.3 (total deficiency).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.total_deficiency`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.total_deficiency` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem total_deficiency {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : DissociationDeficiency.deficiency (graph m n) 4 Finset.univ=2*m+2*n.

**Theorem 1.4 (selected deficiency bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.selected_deficiency_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.selected_deficiency_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selected_deficiency_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (S : Finset (Fin m × Fin n)) : DissociationDeficiency.deficiency (graph m n) 4 S≤2*m+2*n.

**Theorem 1.5 (forming bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_bound {m n : ℕ} (S : Finset (Fin m × Fin n)) (hS : IsMinimalStarForming (graph m n) 2 S) : 7*S.card+(isolates (graph m n) S).card≤4*(m*n)+ DissociationDeficiency.deficiency (graph m n) 4 S.

**Theorem 1.6 (forming perimeter bound).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_perimeter_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_perimeter_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forming_perimeter_bound {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (S : Finset (Fin m × Fin n)) (hS : IsMinimalStarForming (graph m n) 2 S) : 7*S.card+(isolates (graph m n) S).card≤4*(m*n)+2*m+2*n.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.degree_le_four`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.forming_perimeter_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.selected_deficiency_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/GridBoundary.total_deficiency`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DissociationDeficiency](../StarForming/DissociationDeficiency.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation](GridDissociation.md)
