# Drift Stopped2

## Abstract

Stopped log determinant drift and integrability estimates.

Stopped log determinant drift and integrability estimates. The results below relate drift stopped2 to the stochastic ellipsoid construction.

**Theorem 1.1 (norm inv apply le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_inv_apply_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_inv_apply_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖A⁻¹ y‖ ≤ ‖y‖ / m from the quadratic-form lower bound. With x = A⁻¹ y, m‖x‖² ≤ ⟪x, A x⟫ = ⟪x, y⟫ ≤ ‖x‖‖y‖.

**Theorem 1.2 (norm mat To UT sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Frobenius norm of a symmetric matrix, in the model's currency: ‖matToUT M‖² = ∑_{i,j} M_ij².

**Theorem 1.3 (norm apply single sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_apply_single_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_apply_single_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖M eⱼ‖² = ∑ᵢ Mᵢⱼ².

**Theorem 1.4 (sum sq eq sum norm sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.sum_sq_eq_sum_norm_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.sum_sq_eq_sum_norm_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Frobenius norm as a sum of column norms — the shape the bound on V needs.

**Theorem 1.5 (norm mat To UT inv le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_inv_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_inv_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

‖matToUT A⁻¹‖ ≤ √(dim) / m. The Frobenius norm of the inverse is bounded column by column by norm_inv_apply_le, and matToUT is a Frobenius isometry.

**Theorem 1.6 (norm stopped V le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_stoppedV_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_stoppedV_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bound on V — ‖π_k(A_k⁻¹)‖ ≤ √(dim)/m, for the stopped chain, everywhere.

**Theorem 1.7 (stopped Err mid le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.stoppedErr_mid_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.stoppedErr_mid_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The integrand bound at the one disagreeing step. At k = τ − 1 the stopped error is c‖π_kξ_k‖² − ⟪V k, ξ k⟫, and both terms are controlled by ‖ξ k ω‖: the projection is a contraction, and ‖V k‖ ≤ √(dim)/m by §1. This is the integrand whose integral the drift's hbd needs, and it is the only place the stopped error is not ChainWiring.chainErr.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_apply_single_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_inv_apply_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_inv_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_matToUT_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.norm_stoppedV_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.stoppedErr_mid_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped2.sum_sq_eq_sum_norm_sq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Assembly](../../Completion/Assembly.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped](DriftStopped.md)
