# Chain Wiring

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate chain wiring to the stochastic ellipsoid construction.

**Definition 1.1 (q UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.qUT`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.qUT` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The constraint vector of a lattice point: the coordinates of x ⊗ x in the model.

**Theorem 1.2 (sym Mat q UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.symMat_qUT`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.symMat_qUT` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

q x really is x ⊗ x.

**Theorem 1.3 (inner q UT eq quad).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT_eq_quad`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT_eq_quad` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

⟪A, q x⟫ is the quadratic form. So Chain.kSet q W is the set of matrices whose ellipsoid E_A = {v | ⟪A v, v⟫ < 1} (Klartag eq. 9) misses the window, and Chain.freeSub q C is his F_A (eq. 13).

**Theorem 1.4 (inner q UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Non-negative correlation — hinge 1's ⟪x ⊗ x, y ⊗ y⟫ = (x ⬝ᵥ y)², the hypothesis Chain.lift_mem_kSet runs on.

**Definition 1.5 (log Det).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

log det of a point of the model.

**Definition 1.6 (lift Cost).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.liftCost`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.liftCost` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

err: the log-det cost of the correction at one step — the entire discretisation error of the chain.

**Definition 1.7 (pre State).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.preState`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.preState` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's stepped matrix A'_{k+1} before the correction.

**Definition 1.8 (chain Err).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.chainErr`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.chainErr` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's err k.

**Theorem 1.9 (log Det chain succ).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet_chain_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet_chain_succ` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The step's log-determinant splits as the Gaussian part plus the error.

**Theorem 1.10 (measurable Set active eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurableSet_active_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurableSet_active_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The active set is a measurable Finset-valued random variable, fibre by fibre.

**Theorem 1.11 (measurable of active).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_of_active`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_of_active` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Any real function of the active set is a measurable random variable. The active set takes finitely many values (Finset.powerset W), so the composition is a finite sum of indicators.

**Theorem 1.12 (measurable free Dim).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_freeDim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_freeDim` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

N_k = dim F(C_k) is measurable.

**Theorem 1.13 (integrable log Det of bounds).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.integrable_logDet_of_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.integrable_logDet_of_bounds` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

intD from a two-sided bound on the determinant. The lower bound is Klartag eq. (32), det A_t ≥ c_L, from Minkowski's first theorem (det_ge_of_volume_le below); the upper bound is the good event of Corollary 3.2 (H5).

**Definition 1.14 (quad Form).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.quadForm`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.quadForm` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The quadratic form of a matrix, Q_M(v) = ⟪M v, v⟫.

**Theorem 1.15 (inner lift sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_lift_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_lift_sub` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The correction's cost carries no Frobenius norm. With q i = x_i ⊗ x_i, ⟪B, Δ⟫ = ∑_i λ_i · ⟪B x_i, x_i⟫, so the concavity bound on the log-determinant reads ∑_i λ_i ⟪(A')⁻¹ x_i, x_i⟫ ≤ λ_min(A')⁻¹ ∑_i λ_i |x_i|² — one factor of √n cheaper than ‖(A')⁻¹‖_F · ‖Δ‖_F, which is what the Frobenius projection would force.

**Theorem 1.16 (coeff le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.coeff_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.coeff_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Each coefficient is bounded by the step's own increment against that constraint. This is what makes the overshoot O(√h) rather than O(n√h): 1 - ⟪A + B, q i⟫ ≤ -⟪B, q i⟫ because A already satisfies the constraint.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.chainErr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.coeff_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_lift_sub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.inner_qUT_eq_quad`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.integrable_logDet_of_bounds`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.liftCost`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.logDet_chain_succ`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurableSet_active_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_freeDim`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.measurable_of_active`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.preState`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.qUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.quadForm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/ChainWiring.symMat_qUT`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Chain](Chain.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainDrift](ChainDrift.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid](ChainEllipsoid.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/Increments](Increments.md)
