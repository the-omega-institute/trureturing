# Step Second Moment

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate step second moment to the stochastic ellipsoid construction.

**Theorem 1.1 (integral norm coord sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_coord_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_coord_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫ ‖ω k‖² = dim, from StepInputs.integral_norm_sq_starProjection at the whole space.

**Theorem 1.2 (integral norm step sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_step_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_step_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫ ‖ξ_k‖² = c²·dim at the chain's own step.

**Theorem 1.3 (min ge sub sq div).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.min_ge_sub_sq_div`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.min_ge_sub_sq_div` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

min(x, c) ≥ x − x²/c for 0 ≤ x and 0 < c.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_coord_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.integral_norm_step_sq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/StepSecondMoment.min_ge_sub_sq_div`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth](../Gaussian/GaussianFourth.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StepTruncVariance](StepTruncVariance.md)
