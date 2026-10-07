# Assembly

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate assembly to the stochastic ellipsoid construction.

**Theorem 1.1 (sqrt det le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Assembly.sqrt_det_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Assembly.sqrt_det_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag eq. (68), with the constant written out. log det A ≤ C' − 4 log n gives Vol(E_A) ≥ e^{−C'/2}·n²·Vol(Bᴺ). With C' the universal constant of Lemma 5.2 this is c₀ = e^{−C'/2}: the n² of the theorem statement, produced here and nowhere else.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Assembly.sqrt_det_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer](../Construction/LatticeTransfer.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst](../Walk/ChainDataInst.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring](../Walk/ChainWiring.md)
