# Profile Bound4

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound4 to the stochastic ellipsoid construction.

**Theorem 1.1 (integral pow Ioc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.integral_pow_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.integral_pow_Ioc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫₀^ρ r^{n−1} dr = ρⁿ/n.

**Theorem 1.2 (inner ball le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.inner_ball_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.inner_ball_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The inner-ball piece. On (0, ρ] the profile is at most 1/2 (it is exactly 1/2 below the shell), so the piece contributes ρⁿ/(2n).

**Theorem 1.3 (shell subset image).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.shell_subset_image`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.shell_subset_image` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The shell is covered by the window's image. intermediate_value_Ioc, with radiusOf continuous on [0, Y].

**Theorem 1.4 (window split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫₀^W = ∫₀^ρ + ∫_ρ^W, the inner ball plus the shell.

**Theorem 1.5 (window le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The window integral, bounded by the inner ball plus the shell. The shape the final assembly consumes: the fourth piece explicit, the shell handed to integral_shell_le.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.inner_ball_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.integral_pow_Ioc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.shell_subset_image`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound4.window_split`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound3](ProfileBound3.md)
