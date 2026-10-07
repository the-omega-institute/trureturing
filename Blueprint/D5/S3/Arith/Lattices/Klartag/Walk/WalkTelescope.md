# Walk Telescope

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate walk telescope to the stochastic ellipsoid construction.

**Definition 1.1 (pad Inc Vec).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.padIncVec`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.padIncVec` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The padding construction's increment vector. The i-th coordinate is the negated padded increment: the martingale difference ΔM_i plus the padding c_i·η_i.

**Theorem 1.2 (walk Sum padded eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.walkSum_padded_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.walkSum_padded_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

walkSum_padded_eq — Padding.padded_tail_of_increments' hincw, proved. The only proviso is that M 0 is the deterministic constant M₀, which is exactly Klartag's initial gap read at time zero.

**Theorem 1.3 (hprop of hincl).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hprop_of_hincl`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hprop_of_hincl` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The transported Proposition 4.1, with hincw discharged. ChainWalk.tail_of_transport'' and ChainWalk.chainRaw2_of_walk take hprop; this is hprop with everything proved except the padded increment vector's law.

**Theorem 1.4 (hit Set smul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hitSet_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hitSet_smul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The hitting event is scale-invariant. The chain's walk ⟪A_k, q y⟫ − 1 and its normalisation by ‖q y‖ = ‖x‖² — the form yOf's argument is written in — have the same hitting event, so hprop_of_hincl may be read at either.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hitSet_smul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.hprop_of_hincl`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.padIncVec`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope.walkSum_padded_eq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/Padding](../State/Padding.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk](ChainWalk.md)
