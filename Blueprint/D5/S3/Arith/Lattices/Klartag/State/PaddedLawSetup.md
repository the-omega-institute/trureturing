# Padded Law Setup

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate padded law setup to the stochastic ellipsoid construction.

**Theorem 1.1 (std Gaussian prod L2).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.stdGaussian_prodL2`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.stdGaussian_prodL2` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The value-type fact. The standard Gaussian on the L² product *is* the product of the two standard Gaussians — so adjoining the fresh coordinate to the value type is exactly adjoining an independent N(0,1), with no second factor and no reshuffling.

**Definition 1.2 (Tail Side Hyp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.TailSideHyp`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.TailSideHyp` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one probabilistic input of chainRaw2_of_walk, on chainSetup.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.TailSideHyp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup.stdGaussian_prodL2`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainSetup](../Walk/ChainSetup.md)
