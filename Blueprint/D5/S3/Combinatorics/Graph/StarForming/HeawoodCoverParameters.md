# The complete binary-lift parameter dichotomy

## Abstract

The complete binary-lift parameter dichotomy

An explicit isomorphism separates cyclic Heawood labels from binary incidence labels. Every signing has SF sixteen. The six original fifteen-sets transport to every connected signing, giving beta fifteen or sixteen; disconnected signings have beta fourteen by actual disjoint-union additivity. This does not decide which of the other four types attain sixteen, or assert a higher-cover optimum.

**Definition 1.1 (cyclicIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.cyclicIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.cyclicIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def cyclicIso : HeawoodParameters.graph ≃g base.

**Theorem 1.2 (base regular).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.base_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.base_regular` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem base_regular : ∀ v, DegreeCapacity.degree base v=3.

**Theorem 1.3 (sf all).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sf_all`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sf_all` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem sf_all (s : Signing) : SF (graph s) 2=16.

**Definition 1.4 (pack).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.pack`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.pack` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def pack : (Fin 14 × F2) ≃ Fin 28.

**Definition 1.5 (sixIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sixIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sixIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixIso (k : Fin 6) : graph (HeawoodActions.representative k) ≃g HeawoodCertificates.sixGraph k.

**Theorem 1.6 (connected beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.connected_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.connected_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) : 15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16.

**Theorem 1.7 (disconnected beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.disconnected_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.disconnected_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem disconnected_beta (s : Signing) (hs : ¬ (graph s).Preconnected) : beta (graph s) 2=14.

**Theorem 1.8 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (s : Signing) : SF (graph s) 2=16 ∧ (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧ ((graph s).Preconnected → (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.base_regular`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.connected_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.cyclicIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.disconnected_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.pack`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sf_all`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters.sixIso`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/CoverDensity](CoverDensity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodActions](HeawoodActions.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters](HeawoodParameters.md)
