# Padded Law Setup R

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate padded law setup r to the stochastic ellipsoid construction.

**Definition 1.1 (Raw Data R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.RawDataR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.RawDataR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

PaddedLawSetup.RawData at the reach window. Identical field for field except window_lt_p, supp_radius and hwin, which are stated at WindowR.windowR α n.

**Theorem 1.2 (raw Data R mono).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.rawDataR_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.rawDataR_mono` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

RawDataR restricts, exactly as LatticeData.rawData_mono does for RawData: every field is either ∀ y ∈ W or independent of W.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.RawDataR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetupR.rawDataR_mono`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/WindowR](../Completion/WindowR.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](PaddedLawSetup.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddingMap](PaddingMap.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailAtStep](../Tail/TailAtStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailTransport](../Tail/TailTransport.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom](../Walk/ChainInputDom.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWalk](../Walk/ChainWalk.md)
