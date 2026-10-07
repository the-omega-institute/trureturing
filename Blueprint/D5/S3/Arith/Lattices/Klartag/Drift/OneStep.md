# One Step

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate one step to the stochastic ellipsoid construction.

**Theorem 1.1 (log le sub one sub sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_le_sub_one_sub_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_le_sub_one_sub_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The scalar one-step inequality. For 1 ≤ M and 0 < v ≤ M, log v ≤ (v − 1) − (v − 1)² / (2 M). M is sharp: g v = (v−1) − (v−1)²/(2M) − log v has g' v = (v−1)(M−v)/(vM), which changes sign at v = M.

**Theorem 1.2 (trace eq sum eigenvalues real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_eq_sum_eigenvalues_real`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_eq_sum_eigenvalues_real` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

trace of a real Hermitian matrix, with the RCLike.ofReal coercion discharged.

**Theorem 1.3 (spectral real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.spectral_real`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.spectral_real` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The spectral decomposition of a real Hermitian matrix, coercion discharged.

**Theorem 1.4 (det one add eq prod).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.det_one_add_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.det_one_add_eq_prod` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

det (1 + B) = ∏ (1 + λᵢ) for Hermitian B.

**Theorem 1.5 (trace mul self eq sum sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

tr (B * B) = Σ λᵢ² for Hermitian B.

**Theorem 1.6 (trace mul self eq sum sq entries).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq_entries`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq_entries` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

tr (B * B) = Σᵢⱼ Bᵢⱼ² for Hermitian B: the Frobenius norm squared, entrywise.

**Theorem 1.7 (sum sq eigenvalues eq frobenius).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.sum_sq_eigenvalues_eq_frobenius`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.sum_sq_eigenvalues_eq_frobenius` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Frobenius norm squared of a Hermitian matrix is the sum of squares of its eigenvalues.

**Theorem 1.8 (log det one add le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_one_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_one_add_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

One-step inequality after congruence. For Hermitian B whose shifted eigenvalues 1 + λᵢ are positive and bounded above by M ≥ 1, log det (1 + B) ≤ tr B − (Σ λᵢ²)/(2M).

**Theorem 1.9 (log det add le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-step log-det inequality. S is any symmetric congruence factor with S A S = 1 (think S = A^{-1/2}); B = S H S is then A^{-1/2} H A^{-1/2}: log det (A + H) ≤ log det A + tr (A⁻¹ H) − ‖A^{-1/2} H A^{-1/2}‖_F² / (2M) where M ≥ 1 bounds the eigenvalues of A^{-1/2}(A+H)A^{-1/2} from above. This is the discrete replacement for Klartag's Lemma 3.3: summing it along the chain is the Riemann sum of −(1/2)∫ δ_s ds, with no Itô formula and no local-martingale argument.

**Theorem 1.10 (log det add le kappa).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le_kappa`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le_kappa` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The paper's shape: with κ ≥ 1 bounding the eigenvalues of A^{-1/2}(A+H)A^{-1/2}, the quadratic gain is ‖A^{-1/2} H A^{-1/2}‖_F² / (2κ²).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.det_one_add_eq_prod`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_add_le_kappa`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_det_one_add_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.log_le_sub_one_sub_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.spectral_real`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.sum_sq_eigenvalues_eq_frobenius`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_eq_sum_eigenvalues_real`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/OneStep.trace_mul_self_eq_sum_sq_entries`
