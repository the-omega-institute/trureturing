# Chain Data Inst

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain data inst to the stochastic ellipsoid construction.

**Definition 1.1 (chain Data of params).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.chainData_of_params`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.chainData_of_params` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ChainData from the chain's parameters.

**Theorem 1.2 (exists good line of params).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.exists_good_line_of_params`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.exists_good_line_of_params` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The composite. From the chain's parameters to §5's single line g.

**Theorem 1.3 (transfer det of eq68).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.transfer_det_of_eq68`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.transfer_det_of_eq68` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The determinant condition, in Klartag's eq. (68) form. With |det B| = κ_n the transfer's hypothesis reduces to √(det A)·(c·m²) ≤ 1: the chain's det A_T ≤ C/n⁴ with c ≤ C^{-1/2}.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.chainData_of_params`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.exists_good_line_of_params`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainDataInst.transfer_det_of_eq68`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer](../Construction/LatticeTransfer.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Section5](../Construction/Section5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43](../Contact/Lemma43.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift](ChainDrift.md)
