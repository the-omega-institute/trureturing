# Lattice Data R

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate lattice data r to the stochastic ellipsoid construction.

**Theorem 1.1 (tail Side Hyp filter R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.tailSideHyp_filterR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.tailSideHyp_filterR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

TailSideHyp on a restricted window, given a producer at the full window. The producer is a hypothesis because TailSideSetup2.tailSideHyp_of_rawData demands a windowC-shaped RawData; everything else is LatticeData.tailSideHyp_filter's content.

**Theorem 1.2 (mem shell R of shell).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.mem_shellR_of_shell`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.mem_shellR_of_shell` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Coverage at the reach window, with the outer radius written additively.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.mem_shellR_of_shell`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeDataR.tailSideHyp_filterR`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeData](LatticeData.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R](../State/RawDataInst2R.md)
