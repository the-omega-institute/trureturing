# State Invariant2

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate state invariant2 to the stochastic ellipsoid construction.

**Theorem 1.1 (failure le2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.failure_le2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.failure_le2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The union-bound cost at N = ⌈16 n⁷ log n⌉ — Discharge.failure_le's successor at the new N (Discharge.failure_le is stated for ChainWiring.numStepsAdopted, which is frozen).

**Theorem 1.2 (norm lift Step le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.norm_liftStep_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.norm_liftStep_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift at one step is at most the number of newly broken constraints times the step's own increment. The coefficient bound is ChainWiring.coeff_le — 1 − ⟪A + B, q i⟫ ≤ −⟪B, q i⟫ because A already satisfies the constraint — and then Cauchy–Schwarz.

**Theorem 1.3 (scaled map isometry).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.scaled_map_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.scaled_map_isometry` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A linear isometry preserves N(0, c²·Id), not just the standard Gaussian.

**Theorem 1.4 (map prod isometry scaled).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_prod_isometry_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_prod_isometry_scaled` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The frozen rotation at the level of joint laws, for N(0, c²·Id).

**Theorem 1.5 (map frozen isometry scaled).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_frozen_isometry_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_frozen_isometry_scaled` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The frozen rotation preserves the law, at scale c.

**Theorem 1.6 (indep Fun frozen isometry scaled).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.indepFun_frozen_isometry_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.indepFun_frozen_isometry_scaled` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

…and it stays independent of the past, at scale c.

**Theorem 1.7 (chain congr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chain_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chain_congr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain at step k reads only ξ j for j < k.

**Definition 1.8 (past).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.past`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.past` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The past of the increments, truncated at k.

**Definition 1.9 (chain U).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chainU`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chainU` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain read as a function of the past sequence.

**Definition 1.10 (refl Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.reflOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.reflOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The frozen reflection attached to an active set.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chainU`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.chain_congr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.failure_le2`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.indepFun_frozen_isometry_scaled`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_frozen_isometry_scaled`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.map_prod_isometry_scaled`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.norm_liftStep_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.past`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.reflOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant2.scaled_map_isometry`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Discharge](../Completion/Discharge.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/ParamsAdopted2](../Completion/ParamsAdopted2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StateInvariant](StateInvariant.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StepGlue](StepGlue.md)
