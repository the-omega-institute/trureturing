# Actual coordinate relabelings and the six-type transfer

## Abstract

Actual coordinate relabelings and the six-type transfer

The 168 coordinate permutations, their inverses and flag transport are actual graph automorphisms, checked in Lean. A complete finite traceless-matrix conjugator table and the symbolic switching-kernel theorem transport every nonzero signing to one of the original six actual types. The table concerns the complete fixed three-dimensional binary matrix domain; it is not sampling arbitrary cover orders.

**Definition 1.1 (vertexMap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.vertexMap`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.vertexMap` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def vertexMap (g : Fin 168) : Fin 14 → Fin 14.

**Definition 1.2 (inverseIndex).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.inverseIndex`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.inverseIndex` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def inverseIndex : Fin 168 → Fin 168.

**Definition 1.3 (flagMap).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.flagMap`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.flagMap` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def flagMap (g : Fin 168) : Fin 21 → Fin 21.

**Definition 1.4 (automorphism).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.automorphism`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.automorphism` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def automorphism (g : Fin 168) : base ≃g base.

**Definition 1.5 (pull).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.pull`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.pull` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pull (g : Fin 168) (s : Signing) : Signing.

**Definition 1.6 (liftIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.liftIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.liftIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def liftIso (g : Fin 168) (s : Signing) : graph (pull g s) ≃g graph s.

**Definition 1.7 (representative).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.representative`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.representative` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def representative (k : Fin 6) : Signing.

**Definition 1.8 (matrix).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.matrix`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.matrix` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def matrix (a : Fin 8 → F2) : Mat.

**Definition 1.9 (bits).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.bits`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.bits` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def bits (c : Fin 256) (i : Fin 8) : F2.

**Definition 1.10 (actionFor).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.actionFor`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.actionFor` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def actionFor : Fin 256 → Fin 168.

**Definition 1.11 (typeFor).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.typeFor`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.typeFor` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def typeFor : Fin 256 → Fin 6.

**Theorem 1.12 (classification).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.classification` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem classification (M : Mat) (ht : Matrix.trace M=0) (hne : M≠0) : ∃ g : Fin 168, ∃ k : Fin 6, phi (pull g (representative k))=M.

**Theorem 1.13 (six isomorphism).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.six_isomorphism`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.six_isomorphism` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem six_isomorphism (s : Signing) (hs : phi s≠0) : ∃ k : Fin 6, Nonempty (graph s ≃g graph (representative k)).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.actionFor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.automorphism`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.bits`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.classification`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.flagMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.inverseIndex`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.liftIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.matrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.pull`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.representative`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.six_isomorphism`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.typeFor`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodActions.vertexMap`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodLift](HeawoodLift.md)
