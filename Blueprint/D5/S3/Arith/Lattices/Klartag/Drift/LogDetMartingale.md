# Log Det Martingale

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate log det martingale to the stochastic ellipsoid construction.

**Definition 1.1 (mg Incr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgIncr`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgIncr` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The martingale increment Δ_k = ⟪V_k, ξ_k⟫, with V_k the *stopped* π_k(A_k⁻¹).

**Definition 1.2 (mg Part).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgPart`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgPart` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The martingale M_K = ∑_{k<K} Δ_k.

**Theorem 1.3 (strongly Measurable V coord).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_V_coord`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_V_coord` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Each coordinate of V_k is ℱ k-measurable, at the chain's own filtration.

**Theorem 1.4 (strongly Measurable mg Incr).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_mgIncr`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_mgIncr` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Δ_k is ℱ (k+1)-measurable: V_k is ℱ k-measurable and ξ_k is ℱ (k+1)-measurable.

**Theorem 1.5 (abs mg Incr le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.abs_mgIncr_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.abs_mgIncr_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

|Δ_k| ≤ (√n/m)·‖ξ_k‖ — Cauchy–Schwarz against DriftStopped2.norm_stoppedV_le, which holds on every path.

**Theorem 1.6 (integrable mg Incr sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Δ_k² ≤ (n/m²)‖ξ_k‖², so Δ_k is square-integrable.

**Theorem 1.7 (integrable mg Incr mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every product of two increments is integrable — L² × L² ⊆ L¹.

**Theorem 1.8 (cond Exp mg Incr zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.condExp_mgIncr_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.condExp_mgIncr_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[Δ_k | ℱ_k] = 0 — StepInputs2.condExp_inner_eq_zero at the chain's own V_k, exactly as DriftInputsStopped.driftInputs_step_stopped uses it for the drift.

**Theorem 1.9 (integral mg Incr sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgIncr_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgIncr_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[Δ_k²] ≤ h·n/m². 94a's LogDetVariance.condExp_inner_sq gives E[Δ_k² | ℱ_k] = h‖V_k‖² — the *isotropy* is what saves the factor dim; the pointwise bound |Δ_k| ≤ ‖V_k‖‖ξ_k‖ would cost h·d·n/m² instead — and DriftStopped2.norm_stoppedV_le bounds ‖V_k‖² ≤ n/m².

**Theorem 1.10 (integral mg Part sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgPart_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgPart_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[(M_K)²] ≤ K·h·n/m². Expand the square into a double sum, kill every off-diagonal term by orthogonality (§3), and price each diagonal term by §4. E[M_K] = 0, so this is the variance.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.abs_mgIncr_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.condExp_mgIncr_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integrable_mgIncr_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgIncr_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.integral_mgPart_sq_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgIncr`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.mgPart`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_V_coord`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale.stronglyMeasurable_mgIncr`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetVariance](LogDetVariance.md)
