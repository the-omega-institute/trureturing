# Profile Bound5

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound5 to the stochastic ellipsoid construction.

**Theorem 1.1 (image radius Of Ioc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.image_radiusOf_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.image_radiusOf_Ioc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

radiusOf '' (0, Y] = (radiusOf 0, radiusOf Y]. ⊇ is the intermediate value theorem (shell_subset_image); ⊆ is strict monotonicity. Getting the *equality* rather than a containment is what keeps the assembly short: no measurability of an abstract image is needed.

**Theorem 1.2 (shell integral le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_integral_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_integral_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shell integral becomes the I₁/I₂/I₃ integral. integral_shell_eq through the image identity, then integral_shell_le, then integrand_eq_pieces pulls the constant out.

**Theorem 1.3 (hgbound final).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.hgbound_final`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.hgbound_final` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgbound for the concrete profile, with the constant written out: the inner ball, the shift-and-Jacobian factor, and the three pieces.

**Theorem 1.4 (pieces sum le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.pieces_sum_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.pieces_sum_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The three pieces summed, with the prefactor.

**Theorem 1.5 (shell le pieces).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_le_pieces`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_le_pieces` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shell integral, bounded by the three pieces' constant. Composing shell_integral_le with pieces_sum_le: the √t/2 of the former is 1/n times the n√t/2 the pieces carry, which is where the 1/n in C₁ comes from.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.hgbound_final`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.image_radiusOf_Ioc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.pieces_sum_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_integral_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound5.shell_le_pieces`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4](ProfileBound4.md)
