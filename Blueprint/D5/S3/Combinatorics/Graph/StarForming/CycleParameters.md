# Exact all-order cycle parameters

## Abstract

Exact all-order cycle parameters

For every cycle of order at least three, the actual cyclic 110-word with the last vertex omitted has floor(2n/3) vertices and induced degree at most one. Its exact finite counting and the current general degree-capacity upper bound prove beta two and SF two both floor(2n/3), without a parity assumption.

**Definition 1.1 (selection).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def selection (n : ℕ) : Finset (Fin n).

**Theorem 1.2 (selection independent).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_independent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_independent` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_independent (n : ℕ) (hn : 3≤n) : IsKIndependent (SimpleGraph.cycleGraph n) 2 (selection n).

**Theorem 1.3 (selection card).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_card` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selection_card (n : ℕ) : (selection n).card=2*n/3.

**Theorem 1.4 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (n : ℕ) (hn : 3≤n) : beta (SimpleGraph.cycleGraph n) 2=2*n/3 ∧ SF (SimpleGraph.cycleGraph n) 2=2*n/3.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/CycleParameters.selection_independent`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Comparison](Comparison.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
