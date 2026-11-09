# Actual periodic cubic equality cores

## Abstract

Actual periodic cubic equality cores

The actual twenty-vertex cell graph is defined for every finite index type and every index permutation, including fixed points and the empty family. Symbolic neighbor rows prove cubic regularity and a common bipartition. The H/U minimal selection and the explicit matching dissociation selection both have twelve vertices per cell. Global degree capacity and actual attainment prove beta and SF each equal twelve times the cell count. Cyclic connectivity, padding attachments and four-port ring losses are separate obligations.

**Definition 1.1 (graph).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def graph (next : Equiv.Perm I) : SimpleGraph (I × Fin 20).

**Theorem 1.2 (regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem regular (next : Equiv.Perm I) (x : I × Fin 20) : DegreeCapacity.degree (graph next) x = 3.

**Theorem 1.3 (bipartite).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2.

**Theorem 1.4 (exact parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem exact_parameters (next : Equiv.Perm I) : beta (graph next) 2 = 12 * Fintype.card I ∧ SF (graph next) 2 = 12 * Fintype.card I.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.bipartite`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.exact_parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/EqualityCore.regular`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/PrivateClauses](PrivateClauses.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularCompensation](RegularCompensation.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/SubcubicCertificate](SubcubicCertificate.md)
