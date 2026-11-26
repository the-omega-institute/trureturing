# Exact binary private-clause optimization

## Abstract

Exact binary private-clause optimization

Duplicate-free actual closed-neighborhood and oriented-edge clauses characterize minimal two-star formation by hitting and singleton private intersections. The displayed binary integer constraints are equivalent to that predicate, including empty graphs and isolated vertices. The objective has an actual feasible optimizer of value SF and bounds every feasible selection. No solver result is used.

**Definition 1.1 (closed).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.closed`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.closed` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def closed (u : V) : Finset V.

**Definition 1.2 (oriented).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.oriented`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.oriented` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def oriented (u v : V) : Finset V.

**Definition 1.3 (clauses).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clauses`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clauses` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def clauses : Finset (Finset V).

**Theorem 1.4 (clause nonempty).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clause_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clause_nonempty` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem clause_nonempty (E : Finset V) (hE : E ∈ clauses G) : E.Nonempty.

**Theorem 1.5 (minimal iff private).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.minimal_iff_private`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.minimal_iff_private` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_iff_private (S : Finset V) : IsMinimalStarForming G 2 S ↔ (∀ E ∈ clauses G, (S ∩ E).Nonempty) ∧ ∀ v ∈ S, ∃ E ∈ clauses G, S ∩ E = {v}.

**Definition 1.6 (bit).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.bit`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.bit` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bit (b : Bool) : ℕ.

**Definition 1.7 (Feasible).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.Feasible`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.Feasible` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Feasible (S : Finset V) (p : Finset V → Bool) : Prop.

**Theorem 1.8 (feasible iff minimal).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.feasible_iff_minimal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.feasible_iff_minimal` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem feasible_iff_minimal (S : Finset V) : (∃ p, Feasible G S p) ↔ IsMinimalStarForming G 2 S.

**Theorem 1.9 (objective attained).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.objective_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.objective_attained` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem objective_attained : (∃ S p, Feasible G S p ∧ S.card = SF G 2) ∧ ∀ S p, Feasible G S p → S.card ≤ SF G 2.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.Feasible`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.bit`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clause_nonempty`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.clauses`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.closed`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.feasible_iff_minimal`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.minimal_iff_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.objective_attained`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/ClauseModel.oriented`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DegreeCapacity](DegreeCapacity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/DisjointUnion](DisjointUnion.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/FiniteCover](FiniteCover.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
