# The complete binary-lift parameter dichotomy

## Abstract

The complete binary-lift parameter dichotomy

The six original fifteen-sets transport to every connected signing, giving beta fifteen or sixteen. Disconnected signings have beta fourteen. The exact beta values of the other four types and higher-cover optima remain open in this development.

**Definition 1.1 (sixIso).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.sixIso`

*Formalization.* `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.sixIso` (`✓ std3`).

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: def sixIso (k : Fin 6) : graph (HeawoodActions.representative k) ≃g HeawoodCertificates.sixGraph k.

**Theorem 1.2 (connected beta).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) : 15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16.

**Theorem 1.3 (parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem parameters (s : Signing) : SF (graph s) 2=16 ∧ (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧ ((graph s).Preconnected → (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.sixIso`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodActions](HeawoodActions.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters](../HeawoodCoverParameters.md)
