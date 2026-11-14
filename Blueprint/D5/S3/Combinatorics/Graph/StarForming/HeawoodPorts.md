# Saturated ports in the actual broken Heawood block

## Abstract

Saturated ports in the actual broken Heawood block

The original fourteen-vertex broken incidence graph is retained with its exact sparse neighbor rows. Bounded kernel chunks prove that every actual dissociation selection has at most eight vertices; every eight-set contains both ports, each with exactly one selected internal neighbor. The original eight-set and port-omitting seven-set attain their exact sizes. The certificate is local to one fixed block; arbitrary family conclusions are proved by its consumers, without enumerating family size.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph : SimpleGraph (Fin 14).

**Theorem 1.2 (facts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.facts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.facts` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem facts (D : Finset (Fin 14)) (hD : IsKIndependent graph 2 D) : D.card ≤ 8 ∧ (D.card = 8 → 0 ∈ D ∧ 8 ∈ D ∧ DegreeCapacity.selectedDegree graph D 0 = 1 ∧ DegreeCapacity.selectedDegree graph D 8 = 1).

**Definition 1.3 (eightSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.eightSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.eightSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def eightSet : Finset (Fin 14).

**Definition 1.4 (sevenSet).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.sevenSet`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.sevenSet` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sevenSet : Finset (Fin 14).

**Theorem 1.5 (selections).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.selections`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.selections` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem selections : IsKIndependent graph 2 eightSet ∧ eightSet.card = 8 ∧ IsKIndependent graph 2 sevenSet ∧ sevenSet.card = 7 ∧ 0 ∉ sevenSet ∧ 8 ∉ sevenSet.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.eightSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.facts`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.selections`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.sevenSet`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CubicDense](CubicDense.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](HeawoodParameters.md)
