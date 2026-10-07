# Chain Input Dom

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain input dom to the stochastic ellipsoid construction.

**Definition 1.1 (profile At).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom.profileAt`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom.profileAt` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The un-widened profile: profile evaluated at the lattice point's own radius. profile's argument is already shifted inward by √n/2, so undoing that shift is adding √n/2.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainInputDom.profileAt`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform](../Contact/Lemma43Uniform.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/Padding](../State/Padding.md)
