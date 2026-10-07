# Profile Bound2

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound2 to the stochastic ellipsoid construction.

**Theorem 1.1 (mul exp three quarter le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.mul_exp_three_quarter_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.mul_exp_three_quarter_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

x·e^{3x/4 − x²/8} ≤ e⁶. One completed square, (x−7)² + 7 ≥ 0, after log x ≤ x − 1. The sharp constant is e^{2.39}; nothing downstream cares.

**Theorem 1.2 (rpow neg le of le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.rpow_neg_le_of_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.rpow_neg_le_of_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Monotonicity of (1 − s)^{−c} in s: a larger subtraction gives a larger power.

**Theorem 1.3 (integrable On gauss div Ioc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.integrableOn_gauss_div_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.integrableOn_gauss_div_Ioc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Integrability of the shifted Gaussian over y on Ioc A B, A > 0.

**Theorem 1.4 (gaussian over y crude).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.gaussian_over_y_crude`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.gaussian_over_y_crude` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The crude Gaussian bound. ∫_A^B e^{−(y−b)²/2}/y dy ≤ √(2π)/A: no split, just 1/y ≤ 1/A and the total mass.

**Theorem 1.5 (piece le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.piece_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.piece_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The one-dimensional contact integral on an interval (A,B] has the stated Gaussian upper bound whenever A is at least one.

**Theorem 1.6 (I3 le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.I3_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.I3_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

I₃ with its prefactor. b ≤ 2A makes the constant 2·e^J, with no n and no t outside the exponential.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.I3_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.gaussian_over_y_crude`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.integrableOn_gauss_div_Ioc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.mul_exp_three_quarter_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.piece_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2.rpow_neg_le_of_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound](ProfileBound.md)
