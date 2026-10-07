# Walk Measurable

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate walk measurable to the stochastic ellipsoid construction.

**Theorem 1.1 (measurable pure Walk).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_pureWalk`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_pureWalk` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pure walk is measurable — the increment reads the active set through the projection.

**Theorem 1.2 (measurable constraint M).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_constraintM`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_constraintM` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

WalkTelescope.hprop_of_hincl's hM.

**Theorem 1.3 (chain eq of eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.chain_eq_of_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.chain_eq_of_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain reads only the increments before time k.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.chain_eq_of_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_constraintM`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable.measurable_pureWalk`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring](ChainWiring.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope](WalkTelescope.md)
