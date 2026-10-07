# Drift Charge Moments

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate drift charge moments to the stochastic ellipsoid construction.

**Theorem 1.1 (integral mid Cap sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integral_midCap_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integral_midCap_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫ midCap² ≤ K·cstep²·n/m², the same bound variance_M_le carries.

**Theorem 1.2 (integrable mid Cap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integrable_midCap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integrable_midCap` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

midCap itself is integrable: √x ≤ (1 + x)/2.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integrable_midCap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments.integral_midCap_sq_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall](../Walk/StoppedShortfall.md)
