# Raw Data Inst2

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst2 to the stochastic ellipsoid construction.

**Definition 1.1 (id UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.idUT`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.idUT` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The identity matrix in Frobenius coordinates.

**Theorem 1.2 (inner id UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.inner_idUT`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.inner_idUT` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

⟪Id, q x⟫ = |x|².

**Definition 1.3 (A0C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.A0C`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.A0C` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's initial state, Klartag's a₀·Id (eq. 61).

**Definition 1.4 (x Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.xOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.xOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The scaled lattice point, as a plain coordinate vector.

**Definition 1.5 (q C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.qC`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.qC` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's constraint vector at the scaled lattice point.

**Theorem 1.6 (norm Data q C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.normData_qC`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.normData_qC` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

NormData for the chain's own data — both fields, for any W.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.A0C`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.idUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.inner_idUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.normData_qC`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.qC`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2.xOf`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/RawDataInst](RawDataInst.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/TailSideSetup2](../Tail/TailSideSetup2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring](../Walk/ChainWiring.md)
