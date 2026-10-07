# Profile Bound8

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound8 to the stochastic ellipsoid construction.

**Theorem 1.1 (junk le of endpoint).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.junk_le_of_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.junk_le_of_endpoint` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The junk hypothesis, reduced to its endpoint. y ↦ y·s + c·(y·s)² is monotone on y ≥ 0 for s, c ≥ 0, so hJ's ∀ y ∈ Ioc A B follows from the single value at y = B.

**Theorem 1.2 (integrable On shell lhs).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.integrableOn_shell_lhs`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.integrableOn_shell_lhs` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Shape 4's certificate. The change-of-variables integrand is bounded on the window: the Jacobian by window_gap + substDeriv_le, the radius by radiusOf_le_end, the profile by 1/2.

**Theorem 1.3 (hgbound chained).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.hgbound_chained`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.hgbound_chained` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgbound for the concrete profile, chained. shell_integral_le → shell_le_pieces → hgbound_final, with the constant ρⁿ/(2n) + (e^{1/2}/(n·αⁿ))·(K₁ + K₂ + K₃)·e^{n²t/8}, ρ = radiusOf 0. Every hypothesis is now supplied by a lemma of ProfileBound6/ProfileBound7.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.hgbound_chained`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.integrableOn_shell_lhs`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8.junk_le_of_endpoint`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound7](ProfileBound7.md)
