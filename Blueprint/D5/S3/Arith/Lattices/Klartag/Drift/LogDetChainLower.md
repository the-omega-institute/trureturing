# Log Det Chain Lower

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate log det chain lower to the stochastic ellipsoid construction.

**Theorem 1.1 (frobenius sym Mat).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.frobenius_symMat`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.frobenius_symMat` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

symMat is a Frobenius isometry: ∑ᵢⱼ (symMat x)ᵢⱼ² = ‖x‖².

**Theorem 1.2 (log Det add ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_add_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_add_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

LogDetLowerSharp.log_det_add_ge_sharp_of_stateBounds, in EuclideanSpace coordinates.

**Definition 1.3 (incr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-step increment H_j = A_{j+1} − A_j. By StateInvariant.preState_eq and StateInvariant.liftStep it is gaussStep_j + liftStep_j.

**Theorem 1.4 (incr eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

incr = gaussStep + liftStep — the split the martingale and the drift read.

**Theorem 1.5 (log Det chain ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pathwise lower bound on the chain's log-determinant. Pure telescoping: the hypotheses are the state bounds at every index below K and a per-step operator-norm ceiling, both of which goodCut supplies.

**Theorem 1.6 (log Det chain ge split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bound in the shape ShortfallBound.shortfall_le consumes: X ≥ c + M − D with c = logDet A₀, M the trace sum and D the Frobenius sum scaled by κ.

**Theorem 1.7 (norm incr sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.norm_incr_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.norm_incr_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Frobenius sum, dominated by the unprojected steps plus the lift. ‖a + b‖² ≤ (1+ε)‖a‖² + (1+1/ε)‖b‖², and ‖gaussStep_j‖ ≤ ‖ξ_j‖ because it is an orthogonal projection.

**Definition 1.8 (Vcoef).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.Vcoef`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.Vcoef` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's martingale coefficient V_j = π_j (matToUT A_j⁻¹) — the V of StepInputs2.driftInputs_step_chain and of DriftStopped2.norm_stoppedV_le.

**Theorem 1.9 (chain succ eq lift).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.chain_succ_eq_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.chain_succ_eq_lift` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A_{j+1} = lift (preState j).

**Theorem 1.10 (lift Step eq lift sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.liftStep_eq_lift_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.liftStep_eq_lift_sub` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

liftStep j = lift (preState j) − preState j, the shape inner_matToUT_lift_sub_nonneg consumes.

**Theorem 1.11 (trace incr eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.trace_incr_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.trace_incr_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The trace term splits into the martingale increment and the lift's trace cost.

**Theorem 1.12 (inner lift Step nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.inner_liftStep_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.inner_liftStep_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The lift's trace cost is non-negative against A_j⁻¹, which is positive semi-definite on the state bounds. This is what lets the drift's *upper* accounting be dropped entirely in the lower direction: the lift can only raise the log-determinant.

**Theorem 1.13 (log Det chain ge martingale).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_martingale`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_martingale` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The pathwise lower bound, final shape. X ≥ c + M − D with c = logDet A₀, M = ∑_{j<K} ⟪V_j, ξ_j⟫ the martingale and D = κ · ∑_{j<K} ‖H_j‖² the drift proxy. This is exactly ShortfallBound.shortfall_le's hlow.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.Vcoef`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.chain_succ_eq_lift`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.frobenius_symMat`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.incr_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.inner_liftStep_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.liftStep_eq_lift_sub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_add_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_martingale`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.logDet_chain_ge_split`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.norm_incr_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetChainLower.trace_incr_eq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetLowerSharp](LogDetLowerSharp.md)
