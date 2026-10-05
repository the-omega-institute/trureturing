# Good Event

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate good event to the stochastic ellipsoid construction.

**Theorem 1.1 (abs eigenvalues le op Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_eigenvalues_le_opNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_eigenvalues_le_opNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every eigenvalue of a Hermitian matrix is bounded in absolute value by the ℓ² operator norm. Mathlib has the eigenvector basis (Matrix.IsHermitian.mulVec_eigenvectorBasis) but not this bound.

**Theorem 1.2 (abs inner self le op Norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_inner_self_le_opNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_inner_self_le_opNorm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The quadratic form is controlled by the operator norm.

**Theorem 1.3 (pos Def of inner pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_of_inner_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_of_inner_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Positive-definiteness read off the quadratic form on EuclideanSpace.

**Theorem 1.4 (op Norm conj le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_conj_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_conj_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Submultiplicativity of the ℓ² operator norm under congruence, obtained through toEuclideanCLM rather than through the scoped Matrix.Norms.L2Operator instances.

**Theorem 1.5 (pos Def one add).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_one_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_one_add` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

1 + B is positive definite as soon as ‖B‖_op < 1.

**Theorem 1.6 (is Symm of is Hermitian).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.isSymm_of_isHermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.isSymm_of_isHermitian` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For real matrices, Hermitian is symmetric.

**Theorem 1.7 (lower Bound of op Norm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.lowerBound_of_opNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.lowerBound_of_opNorm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

a₀·1 + G ⪰ (a₀ − ‖G‖)·1 in the quadratic-form sense: the shape the good event delivers, since A_k − a₀·Id is the accumulated increment.

**Theorem 1.8 (op Norm sq le of lower Bound).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_sq_le_of_lowerBound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_sq_le_of_lowerBound` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

If A ⪰ m in the quadratic-form sense and S A S = 1 with S symmetric, then ‖S‖_op² ≤ 1/m. With S = A^{-1/2} this is ‖A^{-1/2}‖²_op = λ_min(A)⁻¹.

**Theorem 1.9 (one Step bounds of op Norm le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_bounds_of_opNorm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_bounds_of_opNorm_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H5, eigenvalue half. If the conjugated increment B = S H S has ‖B‖_op ≤ δ < 1 then the two eigenvalue hypotheses of D5.S3.Arith.Lattices.Klartag.log_det_add_le_kappa hold with κ = 1 + δ.

**Theorem 1.10 (pos Def add of conj).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_add_of_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_add_of_conj` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H5, cone half. A + H stays positive definite. The congruence S(A+H)S = 1 + S H S transports posDef_one_add back, using that S is invertible with S⁻¹ = A S = S A.

**Theorem 1.11 (log det step le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.log_det_step_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.log_det_step_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The composed one-step bound. On the good event (‖S H S‖_op ≤ δ < 1) the log-determinant obeys Klartag's Lemma 3.3 in discrete form with κ = 1 + δ, and A + H is still in the cone.

**Theorem 1.12 (one Step of good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_of_good`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_of_good` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H5, end to end. From what the good event supplies — a lower bound m on A's quadratic form and an operator-norm bound η on the increment — the conjugated increment obeys ‖A^{-1/2} H A^{-1/2}‖_op ≤ η/m, so if η/m ≤ δ < 1 both halves of H5 hold and the one-step log-det inequality applies with κ = 1 + δ.

**Definition 1.13 (good Event).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.goodEvent`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.goodEvent` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The good event of Klartag's Proposition 3.4 (p. 16, eq. 43): the accumulated Gaussian part of A_N − a₀·Id has operator norm at most r.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_eigenvalues_le_opNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.abs_inner_self_le_opNorm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.goodEvent`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.isSymm_of_isHermitian`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.log_det_step_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.lowerBound_of_opNorm_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_bounds_of_opNorm_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.oneStep_of_good`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_conj_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.opNorm_sq_le_of_lowerBound`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_add_of_conj`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_of_inner_pos`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent.posDef_one_add`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/OneStep](../Drift/OneStep.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2](../Gaussian/GOETail2.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift](../Walk/ChainDrift.md)
