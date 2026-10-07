# Scaling

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate scaling to the stochastic ellipsoid construction.

**Theorem 1.1 (ereal rhs).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_rhs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_rhs` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The quadratic target volume agrees whether its multiplication is performed in the reals before coercion or directly in the extended reals.

**Theorem 1.2 (ereal coe volume eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_coe_volume_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_coe_volume_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A finite measure equal to ofReal r has extended-real value r when r is nonnegative.

**Theorem 1.3 (volume image ball).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The volume of a linear image of the unit ball is the absolute determinant of the map times the unit-ball volume, including singular maps.

**Theorem 1.4 (volume image ball ne top).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball_ne_top`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball_ne_top` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A linear image of the unit ball in finite-dimensional Euclidean space has finite volume.

**Theorem 1.5 (smul image ball subset).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.smul_image_ball_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.smul_image_ball_subset` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Multiplying a linear map by a scalar of absolute value at most one shrinks its unit-ball image inside the original image.

**Theorem 1.6 (volume smul image ball).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_smul_image_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_smul_image_ball` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Scaling a linear map by a nonnegative scalar t multiplies its unit-ball image volume by t^(n+1).

**Theorem 1.7 (exists volume eq of le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.exists_volume_eq_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.exists_volume_eq_of_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

An ellipsoid that contains no nonzero integer point can be shrunk to any positive target volume at most its own volume, preserving the exact singleton integer-point set.

**Theorem 1.8 (image zero ball).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.image_zero_ball`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.image_zero_ball` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The zero linear map sends the open unit ball to the singleton zero.

**Theorem 1.9 (case zero).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.case_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.case_zero` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The zero map gives the required volume and integer-point set at n=0 for every real packing coefficient.

**Theorem 1.10 (klartag of volume ge).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.klartag_of_volume_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.klartag_of_volume_ge` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A uniform quadratic lower volume bound in every positive natural dimension gives the exact quadratic volume theorem by shrinking; the zero dimension parameter uses the zero map.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.case_zero`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_coe_volume_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.ereal_rhs`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.exists_volume_eq_of_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.image_zero_ball`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.klartag_of_volume_ge`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.smul_image_ball_subset`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_image_ball_ne_top`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Scaling.volume_smul_image_ball`
