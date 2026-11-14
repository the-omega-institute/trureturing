# The actual Fano switching quotient

## Abstract

The actual Fano switching quotient

The twenty-one binary Fano flags define the linear outer-product invariant Phi. Symbolic switching annihilation, an explicit preimage for every traceless matrix, a spanning-tree kernel argument and rank-nullity prove that signings modulo vertex switches are linearly isomorphic to the eight-dimensional traceless matrix space. This is the actual quotient map; graph-switching isomorphisms, conjugacy classification and connectedness transfer remain separate obligations.

**Definition 1.1 (F2).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.F2`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.F2` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev F2.

**Definition 1.2 (Mat).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Mat`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Mat` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Mat.

**Definition 1.3 (Signing).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Signing`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Signing` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Signing.

**Definition 1.4 (Switches).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Switches`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Switches` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: abbrev Switches.

**Definition 1.5 (coordinate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.coordinate`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.coordinate` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def coordinate (p : Fin 7) (j : Fin 3) : F2.

**Definition 1.6 (flags).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def flags : Fin 21 → Fin 7 × Fin 7.

**Theorem 1.7 (flags complete).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags_complete` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem flags_complete : ∀ p l : Fin 7, (∑ j : Fin 3, coordinate p j * coordinate l j) = 0 ↔ ∃! e : Fin 21, flags e = (p,l).

**Definition 1.8 (phi).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def phi : Signing →ₗ[F2] Mat.

**Definition 1.9 (switching).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.switching`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.switching` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def switching : Switches →ₗ[F2] Signing.

**Theorem 1.10 (trace phi).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.trace_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.trace_phi` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem trace_phi (s : Signing) : Matrix.trace (phi s) = 0.

**Theorem 1.11 (phi switching).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_switching`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_switching` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem phi_switching (s : Switches) : phi (switching s) = 0.

**Theorem 1.12 (phi preimage).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_preimage`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_preimage` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem phi_preimage (M : Mat) (hM : Matrix.trace M = 0) : phi (preimage M) = M.

**Definition 1.13 (traceless).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def traceless : Submodule F2 Mat.

**Theorem 1.14 (range phi).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.range_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.range_phi` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem range_phi : LinearMap.range phi = traceless.

**Theorem 1.15 (traceless dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless_dimension` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem traceless_dimension : Module.finrank F2 traceless = 8.

**Theorem 1.16 (kernel phi eq switching).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.kernel_phi_eq_switching`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.kernel_phi_eq_switching` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem kernel_phi_eq_switching : LinearMap.ker phi = LinearMap.range switching.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.F2`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Mat`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Signing`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.Switches`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.coordinate`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.flags_complete`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.kernel_phi_eq_switching`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_preimage`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.phi_switching`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.range_phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.switching`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.trace_phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching.traceless_dimension`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates](HeawoodCertificates.md)
