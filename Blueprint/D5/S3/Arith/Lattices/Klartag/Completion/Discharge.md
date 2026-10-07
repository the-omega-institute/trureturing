# Discharge

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate discharge to the stochastic ellipsoid construction.

**Definition 1.1 (mat To UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.matToUT`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.matToUT` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The coordinate vector of a symmetric matrix — the inverse of Increments.symMat.

**Theorem 1.2 (trace mul eq frobenius).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_eq_frobenius`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_eq_frobenius` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

tr(B H) = ∑_{i,j} B_ij H_ij for symmetric H: the trace term of the one-step inequality is a Frobenius inner product.

**Theorem 1.3 (trace mul sym Mat eq inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_symMat_eq_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_symMat_eq_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The trace term as an inner product. With H = symMat u the step's increment and B a symmetric matrix, tr(B H) = ⟪matToUT B, u⟫ — the form driftInputs_step_chain's V takes.

**Definition 1.4 (State Bounds).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.StateBounds`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.StateBounds` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's state invariant on the good event. A_k is positive definite with a uniform lower bound m on its quadratic form, a uniform upper bound M on its operator norm, and a symmetric congruence factor S with S A_k S = 1.

**Theorem 1.5 (hpt step).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.hpt_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.hpt_step` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hpt for one step and one path. With V k ω = π_k (A_k⁻¹) and c = 1 / (2 M² (1+δ)²), this is exactly the inequality StepInputs2.driftInputs_step_chain consumes.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.StateBounds`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.hpt_step`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.matToUT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_eq_frobenius`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/Discharge.trace_mul_symMat_eq_inner`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Assembly](Assembly.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Completion/Final](Final.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepInputs2](../Walk/StepInputs2.md)
