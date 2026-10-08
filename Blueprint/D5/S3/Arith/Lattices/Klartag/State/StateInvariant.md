# State Invariant

## Abstract

Symmetric matrix state invariants and padded driving laws.

Symmetric matrix state invariants and padded driving laws. The results below relate state invariant to the stochastic ellipsoid construction.

**Definition 1.1 (gauss Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussStep`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussStep` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The projected Gaussian part of one step.

**Definition 1.2 (lift Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.liftStep`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.liftStep` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-sided lift applied at one step.

**Theorem 1.3 (chain fst eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.chain_fst_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.chain_fst_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The decomposition. A_k = A₀ + (accumulated projected Gaussian) + (accumulated lifts).

**Definition 1.4 (scaled).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

N(0, c²·Id) on E: the standard Gaussian scaled by c.

**Theorem 1.5 (scaled conv scaled).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled_conv_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled_conv_scaled` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The convolution identity: N(0,a²) ∗ N(0,b²) = N(0,a²+b²) on E.

**Theorem 1.6 (star Projection add self).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.starProjection_add_self`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.starProjection_add_self` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

π x + π x = x + R x with R = Submodule.reflection K: the Maurey split at one step.

**Definition 1.7 (refl Step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.reflStep`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.reflStep` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The reflected increment R_j ξ_j, R_j = π_j − π̃_j.

**Theorem 1.8 (gauss Sum add self).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussSum_add_self`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussSum_add_self` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Maurey split, accumulated: 2 Σ_{j<k} π_j ξ_j = Σ_{j<k} ξ_j + Σ_{j<k} R_j ξ_j. Both sums on the right are over *unprojected* increments, which is what makes the induction possible.

**Theorem 1.9 (op Norm gauss Sum le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.opNorm_gaussSum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.opNorm_gaussSum_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Hence the accumulated projected sum is dominated by the two halves.

**Theorem 1.10 (measure Real op Norm sym Mat ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.measureReal_opNorm_symMat_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.measureReal_opNorm_symMat_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Corollary 3.2 for a scaled standard Gaussian on the UT n carrier. If Z has law N(0, ρ²·Id) then its symmetric matrix obeys Klartag's operator-norm tail.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.chain_fst_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.gaussSum_add_self`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.liftStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.measureReal_opNorm_symMat_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.opNorm_gaussSum_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.reflStep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.scaled_conv_scaled`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/State/StateInvariant.starProjection_add_self`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Discharge](../Completion/Discharge.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/State/StepGlue](StepGlue.md)
