# Padded Law Setup RW2

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate padded law setup rw2 to the stochastic ellipsoid construction.

**Definition 1.1 (Raw Data R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.RawDataR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.RawDataR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

PaddedLawSetup.RawData at the reach window. Identical field for field except window_lt_p, supp_radius and hwin, which are stated at WindowR2.windowR2 α n.

**Theorem 1.2 (raw Data R mono).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.rawDataR_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.rawDataR_mono` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

RawDataR restricts, exactly as LatticeData.rawData_mono does for RawData: every field is either ∀ y ∈ W or independent of W.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.RawDataR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupRW2.rawDataR_mono`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR2](../Completion/WindowR2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](PaddedLawSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalkRW2](../Walk/ChainWalkRW2.md)
