# Chain Shortfall

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain shortfall to the stochastic ellipsoid construction.

**Theorem 1.1 (hshort at chain).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainShortfall.hshort_at_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainShortfall.hshort_at_chain` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hshort at the chain, in the shape CutVariance.goodPathCut_var binds, with L = logDet A₀ − (driftCen + s) − t. Every hypothesis below is a parameter of the chain or a sign condition; no probabilistic fact is left.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainShortfall.hshort_at_chain`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal](../Drift/DriftChargeTotal.md)
