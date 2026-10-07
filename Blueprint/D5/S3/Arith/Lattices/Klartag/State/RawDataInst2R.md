# Raw Data Inst2R

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst2r to the stochastic ellipsoid construction.

**Definition 1.1 (shell R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.shellR`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.shellR` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's window at the reach: the integer points between (1−1/n)/α (exclusive) and windowR α n − √n/2 (inclusive).

**Theorem 1.2 (inner radius R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.inner_radiusR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.inner_radiusR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The inner radius, unscaled, on the reach shell.

**Theorem 1.3 (a0C mul sq gt one of inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.a0C_mul_sq_gt_one_of_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.a0C_mul_sq_gt_one_of_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

a₀·(α‖toE y‖)² > 1 from the inner radius alone — the window plays no part, so this serves both lanes.

**Theorem 1.4 (lattice fields R).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.lattice_fieldsR`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.lattice_fieldsR` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The seven lattice fields, for the chain's own q, A₀ and the reach shell.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.a0C_mul_sq_gt_one_of_inner`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.inner_radiusR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.lattice_fieldsR`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/RawDataInst2R.shellR`
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/RawDataInst2](RawDataInst2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/RawDataInstR](RawDataInstR.md)
