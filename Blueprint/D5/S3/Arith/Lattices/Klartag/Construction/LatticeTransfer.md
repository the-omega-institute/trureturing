# Lattice Transfer

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate lattice transfer to the stochastic ellipsoid construction.

**Theorem 1.1 (zero mem ellipsoid).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.zero_mem_ellipsoid`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.zero_mem_ellipsoid` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The origin is in every ellipsoid.

**Theorem 1.2 (mem ellipsoid congr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.mem_ellipsoid_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.mem_ellipsoid_congr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The congruence A ↦ Bᵀ A B pulls the ellipsoid back along B.

**Theorem 1.3 (det congr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.det_congr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.det_congr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

det (Bᵀ A B) = det(B)² det(A).

**Theorem 1.4 (congr factor).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.congr_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.congr_factor` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The congruence factor transports: S' = B⁻¹ S works for A' = Bᵀ A B.

**Theorem 1.5 (integer Points eq zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.integerPoints_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.integerPoints_eq_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H10 — the lattice transfer. If E_A contains no non-zero point of the lattice B(ℤⁿ), then the congruent ellipsoid E_{BᵀAB} contains no non-zero point of ℤⁿ. This is ChainEllipsoid.klartag_of_chain's last conjunct.

**Theorem 1.6 (chain hyp of transfer).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.chain_hyp_of_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.chain_hyp_of_transfer` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H10, packaged for klartag_of_chain. From an L-free ellipsoid in the lattice frame (L = B(ℤⁿ)) to the hypothesis body of ChainEllipsoid.klartag_of_chain in the integer frame.

**Theorem 1.7 (exists basis Matrix).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.exists_basisMatrix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.exists_basisMatrix` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The basis matrix. Every ℤ-lattice of full rank in Fin n → ℝ is B(ℤⁿ) for an invertible real matrix B. Stated for an arbitrary lattice (rule 7), not for Construction A: D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA.latR carries the two instances, so this applies to it directly.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.chain_hyp_of_transfer`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.congr_factor`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.det_congr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.exists_basisMatrix`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.integerPoints_eq_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.mem_ellipsoid_congr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer.zero_mem_ellipsoid`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid](../Walk/ChainEllipsoid.md)
