# Trunc Sum Mean

## Abstract

Uniform constants and completion of lattice packing.

Uniform constants and completion of lattice packing. The results below relate trunc sum mean to the stochastic ellipsoid construction.

**Theorem 1.1 (integral sum sq Trunc ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[G] from below. G = ∑_{k<K} min(‖ξ_k‖², cap), so the per-step bound sums.

**Theorem 1.2 (drift Cen ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.driftCen_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.driftCen_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

driftCen from below. The shape hLb consumes: the centre is at least κ(1+ε) times the summed lower bound, the (1+1/ε)(c₃η)² piece being non-negative.

**Theorem 1.3 (eta Adopted sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.etaAdopted_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.etaAdopted_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

η² = 2·h·dim·n at the adopted parameters.

**Theorem 1.4 (horizon mul card ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.horizon_mul_card_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.horizon_mul_card_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

T·dim ≥ 8·log n — the drift scale, from below. horizon n = 16·log n/n² and card (UT n) = n(n+1)/2, so the product is 8·log n·(n+1)/n. With κ ≥ 1/2 and 1 + ε ≥ 1, driftCen_ge_adopted then gives driftCen ≥ 4·log n·(1 − 50/n), which is exactly what hLb needs against the −4·log n on the other side.

**Theorem 1.5 (integral sum sq Trunc le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[G] from above, the companion hbudget needs: the truncation only lowers, so ∫ min(‖ξ_k‖², cap) ≤ ∫ ‖ξ_k‖² = c²·dim, and summing gives K·c²·dim = T·dim at K = N.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.driftCen_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.etaAdopted_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.horizon_mul_card_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Completion/TruncSumMean.integral_sum_sqTrunc_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal](../Drift/DriftChargeTotal.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment](../Walk/StepSecondMoment.md)
