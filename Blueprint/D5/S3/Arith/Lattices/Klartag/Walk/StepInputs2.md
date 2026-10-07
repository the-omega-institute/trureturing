# Step Inputs2

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate step inputs2 to the stochastic ellipsoid construction.

**Theorem 1.1 (op Norm le frobenius).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_le_frobenius`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_le_frobenius` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The operator norm is at most the Frobenius norm, row by row by Cauchy–Schwarz. Mathlib has the two norms (Matrix.toEuclideanCLM, Matrix.frobenius_norm) but not this comparison in a form free of the scoped Matrix.Norms instances.

**Theorem 1.2 (op Norm sym Mat le norm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_le_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_le_norm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

In the model of R^{n×n}_sym, the Frobenius norm of symMat x *is* the Euclidean norm of the coordinate vector x (Increments.sum_symMat_mul_eq_inner), so the operator norm of the matrix is at most ‖x‖.

**Theorem 1.3 (op Norm sym Mat star Projection le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_starProjection_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_starProjection_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The per-step bound in the currency oneStep_of_good consumes: the orthogonal projection contracts the Euclidean norm, so the operator norm of the projected increment is at most the norm of the increment.

**Theorem 1.4 (measure Real abs ge le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_abs_ge_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_abs_ge_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Two-sided Gaussian tail.

**Theorem 1.5 (measure Real norm ge le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_norm_ge_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_norm_ge_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Euclidean-norm tail by a coordinate union bound. No independence is used: the coordinates only have to be marginally N(0, v).

**Definition 1.6 (step Good).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.stepGood`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.stepGood` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The set on which every step has a small increment. This is the second half of the good event: GoodEvent.goodEvent controls the *accumulated* sum, this controls each single step, and GoodEvent.oneStep_of_good needs both.

**Theorem 1.7 (measure Real compl step Good le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_compl_stepGood_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_compl_stepGood_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The union bound over the N steps. Cost N · d · 2 · exp(−η²/(2 d v)).

**Theorem 1.8 (cond Exp inner eq zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_inner_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_inner_eq_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

H2 — the centred increment kills the middle term of the one-step inequality.

**Theorem 1.9 (sum inner star Projection).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.sum_inner_starProjection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.sum_inner_starProjection` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The trace of an orthogonal projection is the dimension of its range, in the elementary ∑_p ⟪b p, π (b p)⟫ form. Mathlib has LinearMap.IsProj.trace but not this, and not the bridge from LinearMap.trace to an orthonormal-basis sum.

**Theorem 1.10 (norm star Projection sq eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.norm_starProjection_sq_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.norm_starProjection_sq_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The quadratic form of an orthogonal projection, in coordinates.

**Theorem 1.11 (cond Exp quad Form).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_quadForm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_quadForm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The conditional expectation of a quadratic form in the increment with ℱ-measurable coefficients.

**Theorem 1.12 (integral coord eq zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_eq_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The increment's coordinates are centred.

**Theorem 1.13 (integral coord mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The covariance of the increment's coordinates.

**Theorem 1.14 (log det step unconj).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.log_det_step_unconj`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.log_det_step_unconj` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-step bound with the unconjugated quadratic gain. GoodEvent.oneStep_of_good produces -‖S H S‖²_F / (2(1+δ)²); the conversion turns it into -‖H‖²_F / (2 M² (1+δ)²), which is the shape whose conditional expectation H3 computes.

**Theorem 1.15 (inner star Projection swap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.inner_starProjection_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.inner_starProjection_swap` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

⟪u, π x⟫ = ⟪π u, x⟫: the form in which the chain's middle term ⟪A_k⁻¹, π_k ξ_k⟫ = ⟪π_k A_k⁻¹, ξ_k⟫ is fed to H2, whose V is then π_k A_k⁻¹.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_inner_eq_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.condExp_quadForm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.inner_starProjection_swap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_eq_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.integral_coord_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.log_det_step_unconj`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_abs_ge_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_compl_stepGood_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.measureReal_norm_ge_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.norm_starProjection_sq_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_le_frobenius`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_le_norm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.opNorm_symMat_starProjection_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.stepGood`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2.sum_inner_starProjection`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/GoodEvent](../Completion/GoodEvent.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Increments](Increments.md)
