# Lemma43Uniform

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43uniform to the stochastic ellipsoid construction.

**Theorem 1.1 (Phi C y Of mono).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.PhiC_yOf_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.PhiC_yOf_mono` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

t ↦ PhiC (yOf a₀ t u) is monotone: yOf is c/√t, which decreases in t when c ≥ 0 (and PhiC is antitone), while for c < 0 both values are negative and PhiC is 1/2 at both.

**Theorem 1.2 (profile mono time).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.profile_mono_time`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.profile_mono_time` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The profile is monotone in t. This is what the small-t branch runs on.

**Theorem 1.3 (radius Of zero eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_zero_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_zero_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

radiusOf at y = 0 is t-free: this is why Lemma 4.3's inner-ball term is a constant.

**Theorem 1.4 (radius Of y Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_yOf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_yOf` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

radiusOf inverts yOf. This is the reparameterisation.

**Definition 1.5 (rho C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.rhoC`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.rhoC` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

radiusOf a₀ α (√n/2) t 0, written t-free.

**Definition 1.6 (Kc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.Kc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.Kc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

pieces_at_params' constant: K = e⁶ + e³(2/√(2π) + 2) + 2e³.

**Theorem 1.7 (integrable radial euclidean).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.integrable_radial_euclidean`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.integrable_radial_euclidean` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Params.integrable, discharged.

**Definition 1.8 (a0C).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.a0C`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.a0C` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag's a₀ = (1 − 1/n)⁻², p. 21 eq. (61).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.Kc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.PhiC_yOf_mono`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.a0C`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.integrable_radial_euclidean`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.profile_mono_time`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_yOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.radiusOf_zero_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Uniform.rhoC`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43Final](Lemma43Final.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ProfileBound8](ProfileBound8.md)
