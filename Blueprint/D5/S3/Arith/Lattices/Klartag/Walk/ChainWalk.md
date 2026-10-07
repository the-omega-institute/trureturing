# Chain Walk

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain walk to the stochastic ellipsoid construction.

**Definition 1.1 (pure Walk).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pure constraint walk: ⟪A₀, q j⟫ plus the martingale increments only, with the one-sided lift dropped.

**Theorem 1.2 (constraint walk eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraint_walk_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraint_walk_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's defining equation. Along one step the constraint value ⟪A_k, q j⟫ moves by the martingale increment ⟪π_k ξ_k, q j⟫ plus the one-sided lift term.

**Theorem 1.3 (lift term nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.lift_term_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.lift_term_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift is one-sided. Every summand is non-negative, because a violated constraint has ⟪A', q i⟫ < 1 and the constraint vectors are non-negatively correlated.

**Theorem 1.4 (pure Walk le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pure walk is below the constraint value. The lift only pushes constraints up.

**Theorem 1.5 (pure Walk le one of mem).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le_one_of_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le_one_of_mem` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The containment. If j is active at step k, the *pure* walk has already reached the boundary 1 by step k — so the contact event sits inside the padded walk's hitting event.

**Theorem 1.6 (pure Walk succ sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_succ_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_succ_sub` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pure walk's increment, read against the increment: the projection is self-adjoint, so the martingale increment is ⟪ξ_k, π_k (q j)⟫ — an inner product against a past-measurable vector, which is what PaddingMap.padInc consumes.

**Definition 1.7 (constraint M).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraintM`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraintM` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's scalar martingale for a window point, normalised so that the constraint's boundary is 0. M_0 = ⟪A₀, q j⟫ − 1 is Klartag's initial gap, eq. (61).

**Theorem 1.8 (chain hhit).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.chain_hhit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.chain_hhit` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The containment, in TailTransport.tail_at_step_μ's shape.

**Definition 1.9 (contact Set).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.contactSet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.contactSet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Abbreviation: the chain's accumulated contact set.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.chain_hhit`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraintM`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.constraint_walk_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.contactSet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.lift_term_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_le_one_of_mem`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk.pureWalk_succ_sub`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddingMap](../State/PaddingMap.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Chain](Chain.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring](ChainWiring.md)
