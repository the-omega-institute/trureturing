# Raw Data Inst

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst to the stochastic ellipsoid construction.

**Theorem 1.1 (exists prime alpha mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst.exists_prime_alpha_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst.exists_prime_alpha_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The prime choice. Section5.exists_prime_alpha_le with the threshold chosen so that the *product* α·p clears any prescribed M. Everything RawData asks of p and α beyond the lattice data reduces to a lower bound on α·p, because (α·p)^n = κ_n·p.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst.exists_prime_alpha_mul`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Section5](../Construction/Section5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform](../Contact/Lemma43Uniform.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/PaddedLawSetup](PaddedLawSetup.md)
