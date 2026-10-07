# Profile Bound6

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound6 to the stochastic ellipsoid construction.

**Theorem 1.1 (rpow factor le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.rpow_factor_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.rpow_factor_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The uniform bound on the window. y·√t ≤ 1/2 gives (1 − y√t)^{−c} ≤ (1/2)^{−c}, with no n and no t in it.

**Theorem 1.2 (integrable On pieces).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_pieces`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_pieces` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

I₁/I₂/I₃'s hint1, and pieces_sum_le's i1, i2, i3. Bounded by (1/2)·(1/2)^{−(n+2)/2} on the window, measurable, finite measure.

**Theorem 1.3 (integrable On rhs).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_rhs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_rhs` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

I₂'s and I₃'s hint2. On Ioc A B with A ≥ 1 the factor 1/y is at most 1, so the whole integrand is bounded by its constant times 1.

**Theorem 1.4 (integrable On profile sub).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_profile_sub`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_profile_sub` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgbound_final's h1 and h2. integrableOn_profile_radial restricted.

**Theorem 1.5 (subst Deriv le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.substDeriv_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.substDeriv_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Jacobian is bounded where a₀ − √t·y is bounded away from zero.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_pieces`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_profile_sub`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.integrableOn_rhs`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.rpow_factor_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound6.substDeriv_le`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5](ProfileBound5.md)
