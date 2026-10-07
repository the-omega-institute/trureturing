# Profile Bound3

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound3 to the stochastic ellipsoid construction.

**Theorem 1.1 (y Of subst).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.yOf_subst`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.yOf_subst` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

yOf a₀ t (subst a₀ √t y) = y: the substitution is a right inverse of the paper's y(r).

**Definition 1.2 (radius Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.radiusOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.radiusOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The radius at which the profile takes the value Φ(y): the paper's substitution, un-scaled by α and shifted out by the cube radius δ.

**Theorem 1.3 (profile radius Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.profile_radiusOf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.profile_radiusOf` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The profile at the substituted radius is Φ. Both if-branches take their non-degenerate values — the radius is inside the window, and the shifted, scaled radius is positive — and yOf_subst collapses the rest.

**Theorem 1.4 (substituted integrand le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.substituted_integrand_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.substituted_integrand_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The substituted integrand, with the shift priced. Combining subst_integrand (the Jacobian and the r^{n−1} factor) with shift_constant (the cube shift, bounded by e^{1/2} under tiling_defect) and rpow_neg_le_of_one_le (normalising a₀ away). The right-hand side is exactly the integrand of I₁, I₂ and I₃, times e^{1/2}·√t/(2·αⁿ).

**Theorem 1.5 (integrand eq pieces).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.integrand_eq_pieces`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.integrand_eq_pieces` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

PhiC = Φ on the positive reals, so the bound of integral_shell_le is the I₁/I₂/I₃ integrand with the constant e^{1/2}·√t/(2αⁿ) in front.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.integrand_eq_pieces`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.profile_radiusOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.radiusOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.substituted_integrand_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3.yOf_subst`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound2](ProfileBound2.md)
