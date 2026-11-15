# Actual closed-core omission accounting

## Abstract

Actual closed-core omission accounting

The twenty-vertex graph R retains its complete high six-cycle and only the two specified outside edges. Each Valid and Across inequality is extracted from an actual three-vertex path in an arbitrary dissociation selection. Full-pair indicators implement the score-preserving singleton normalization. The original cell proof gives cardinality plus the number of wholly omitted designated pairs at most twelve, without restrictions at either interface vertex or reused neighboring credits.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 20).

**Definition 1.2 (bit).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.bit`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.bit` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bit (S : Finset (Fin 20)) (f : Bool) (v : Fin 20) : ℕ.

**Definition 1.3 (full).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.full`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.full` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def full (S : Finset (Fin 20)) (f : Bool) (a b : Fin 20) : ℕ.

**Definition 1.4 (cell).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.cell`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.cell` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cell (S : Finset (Fin 20)) (f : Bool) : Fin 3 → Cell.

**Definition 1.5 (omitted).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omitted`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omitted` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def omitted (S : Finset (Fin 20)) (f : Bool) : ℕ.

**Theorem 1.6 (omission bound).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omission_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omission_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omission_bound (S : Finset (Fin 20)) (hS : IsKIndependent graph 2 S) : S.card+omitted S false≤12.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.bit`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.cell`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.full`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omission_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClosedCore.omitted`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle](ClosedHighCycle.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts](HeawoodPorts.md)
