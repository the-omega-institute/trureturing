# Profile Bound

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate profile bound to the stochastic ellipsoid construction.

**Theorem 1.1 (lintegral profile eq of Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.lintegral_profile_eq_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.lintegral_profile_eq_ofReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The ℝ≥0∞ integral of the profile is the ofReal of its Bochner integral.

**Theorem 1.2 (hgbound of bochner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_bochner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_bochner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

hgbound from a real bound. Everything ℝ≥0∞ is discharged here, so the three-piece split may be carried out entirely over ℝ.

**Theorem 1.3 (hgbound of window).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_window`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_window` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The same, restricted to the window — the form the split consumes.

**Theorem 1.4 (pow add le exp mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.pow_add_le_exp_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.pow_add_le_exp_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(u + c)^m ≤ e^{m·c/u₀}·u^m for u ≥ u₀ > 0 and c ≥ 0.

**Theorem 1.5 (set Integral Ioc split).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.setIntegral_Ioc_split`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.setIntegral_Ioc_split` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Two-piece additivity on Ioc.

**Theorem 1.6 (I2 le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.I2_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.I2_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

I₂ with its prefactor, bounded by an absolute constant times e^{n²t/8}. This is Klartag's eq. (59) together with eq. (56)'s prefactor, complete. The constant is e^J·(2/√(2π) + 2), where J bounds the junk term of Lemma43.integrand_le on (1, L].

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.I2_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_bochner`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.hgbound_of_window`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.lintegral_profile_eq_ofReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.pow_add_le_exp_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound.setIntegral_Ioc_split`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Profile](Profile.md)
