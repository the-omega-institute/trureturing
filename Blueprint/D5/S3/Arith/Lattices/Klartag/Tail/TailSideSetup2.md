# Tail Side Setup2

## Abstract

Lattice tail bounds along the matrix walk.

Lattice tail bounds along the matrix walk. The results below relate tail side setup2 to the stochastic ellipsoid construction.

**Theorem 1.1 (measurable of active vec).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.measurable_of_active_vec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.measurable_of_active_vec` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ChainWiring.measurable_of_active, vector-valued. A statistic of the active set alone is measurable; the proof is the same finite partition over W.powerset.

**Definition 1.2 (extendc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.extendc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.extendc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A truncated past, read back as a full path at scale c.

**Definition 1.3 (dir Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.dirOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.dirOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's projected direction at q y, normalised.

**Definition 1.4 (Norm Data).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.NormData`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.NormData` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The two identities RawData does not carry: Klartag's eq. (61) at time zero. Both are immediate for the chain's own q y = ChainWiring.qUT (α • toE n y) and A₀ = a0C n • Id.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.NormData`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.dirOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.extendc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2.measurable_of_active_vec`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup](TailSideSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/WalkMeasurable](../Walk/WalkMeasurable.md)
