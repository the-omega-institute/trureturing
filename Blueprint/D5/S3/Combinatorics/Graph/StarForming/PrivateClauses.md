# Exact clauses and private ownership

## Abstract

Exact clauses and private ownership

The monotone clauses are the closed neighborhood at a vertex and, for each oriented actual edge, the union of the first endpoint with the other neighbors of both endpoints. Formation is exactly clause hitting; inclusion-minimality is exactly existence of a private clause for every selected vertex. A clause has at most one private owner. The boundary certificate distinguishes an internal private clause from support through a selected boundary port.

**Definition 1.1 (Clause).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Clause`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Clause` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: inductive Clause (Vertex : Type).

**Definition 1.2 (Valid).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Valid`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Valid` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Valid {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Clause Vertex → Prop | .closed _ => True | .oriented center neighbor => adjacency center neighbor def Support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Clause Vertex → Vertex → Prop | .closed center, vertex => vertex = center ∨ adjacency center vertex | .oriented center neighbor, vertex => vertex = center ∨ (adjacency center vertex ∧ vertex ≠ neighbor) ∨ (adjacency neighbor vertex ∧ vertex ≠ center) def Hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.3 (Support).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Support`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Support` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Clause Vertex → Vertex → Prop | .closed center, vertex => vertex = center ∨ adjacency center vertex | .oriented center neighbor, vertex => vertex = center ∨ (adjacency center vertex ∧ vertex ≠ neighbor) ∨ (adjacency neighbor vertex ∧ vertex ≠ center) def Hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.4 (Hits).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Hits`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Hits` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Prop.

**Definition 1.5 (Private).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Private`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Private` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def Private {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (clause : Clause Vertex) (owner : Vertex) : Prop.

**Theorem 1.6 (forms iff hits).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.forms_iff_hits`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.forms_iff_hits` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem forms_iff_hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Forms adjacency selection ↔ Hits adjacency selection.

**Theorem 1.7 (minimal iff private).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.minimal_iff_private`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.minimal_iff_private` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem minimal_iff_private {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) : Minimal adjacency selection ↔ Hits adjacency selection ∧ ∀ owner, selection owner → ∃ clause, Private adjacency selection clause owner.

**Theorem 1.8 (private owner unique).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.private_owner_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.private_owner_unique` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem private_owner_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop) (clause : Clause Vertex) (first second : Vertex) (hfirst : selection first) (_hsecond : selection second) (hprivateFirst : Private adjacency selection clause first) (hprivateSecond : Private adjacency selection clause second) : first = second.

**Theorem 1.9 (support mono).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.support_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.support_mono` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem support_mono {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (hinclusion : ∀ first second, inside first second → ambient first second) (clause : Clause Vertex) (vertex : Vertex) (hsupport : Support inside clause vertex) : Support ambient clause vertex.

**Definition 1.10 (PortWitness).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.PortWitness`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.PortWitness` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def PortWitness {Vertex : Type} (inside : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (candidate : Vertex) : Prop.

**Theorem 1.11 (boundary certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.boundary_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.boundary_certificate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem boundary_certificate {Vertex : Type} (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop) (hinclusion : ∀ first second, inside first second → ambient first second) (hinside : ∀ first second, inside first second → core first ∧ core second) (hsymmInside : ∀ first second, inside first second → inside second first) (hsymmAmbient : ∀ first second, ambient first second → ambient second first) (hunchanged : ∀ vertex, core vertex → ¬ port vertex → ∀ neighbor, ambient vertex neighbor → inside vertex neighbor) (hminimal : Minimal ambient selection) (candidate : Vertex) (hcore : core candidate) (hnonport : ¬ port candidate) (hselected : selection candidate) : (∃ clause, Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate) ∨ PortWitness inside core port selection candidate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Clause`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Hits`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.PortWitness`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Private`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Support`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.Valid`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.boundary_certificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.forms_iff_hits`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.minimal_iff_private`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.private_owner_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/PrivateClauses.support_mono`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/RegularBound](RegularBound.md)
