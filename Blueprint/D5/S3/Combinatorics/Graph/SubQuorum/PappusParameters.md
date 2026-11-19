# Exact Pappus maxima

## Abstract

Exact Pappus maxima

The representative maximum Omega and the sub-quorum parameter psiSq of the Pappus graph are both ten. These positive certificates are outside the proof of the beta half-order refutation and have no qualifying refutation basis.

**Theorem 1.1 (Omega upper from all feasible pairs).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_upper_of_objective_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_upper_of_objective_bound` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omega_upper_of_objective_bound (n : ℕ) (h : ∀ T M, Feasible G T M → T.card + M.card ≤ n) : Omega G ≤ n. The finite Pappus maximum is its actual consumer.

**Theorem 1.2 (omega pappus).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_pappus`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_pappus` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem omega_pappus : Omega pappusGraph = 10.

**Theorem 1.3 (pappus parameters).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.pappus_parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.pappus_parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Exact declaration: theorem pappus_parameters : beta pappusGraph 2 = 10 ∧ psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_pappus`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.omega_upper_of_objective_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.pappus_parameters`
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4FreeRepresentatives](C4FreeRepresentatives.md)
- Dependency: [D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds](C4RepresentativeBounds.md)
