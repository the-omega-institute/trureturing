# Drift Charge Total

## Abstract

Second order log determinant bounds and accumulated drift.

Second order log determinant bounds and accumulated drift. The results below relate drift charge total to the stochastic ellipsoid construction.

**Definition 1.1 (drift Charge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCharge`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCharge` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The drift charge, exactly the bracket of StoppedShortfall.logDet_stopped_ge_final.

**Definition 1.2 (drift Cen).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCen`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCen` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The centring constant: the mean of the chi-square half only.

**Theorem 1.3 (integral drift Charge sub cen sq le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.integral_driftCharge_sub_cen_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.integral_driftCharge_sub_cen_sq_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The centred second moment.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCen`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.driftCharge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeTotal.integral_driftCharge_sub_cen_sq_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/DriftChargeMoments](DriftChargeMoments.md)
