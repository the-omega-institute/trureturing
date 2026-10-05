# Lemma43C

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43c to the stochastic ellipsoid construction.

**Theorem 1.1 (integral exp mul Ioc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_mul_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_mul_Ioc` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

∫₀^T e^{c·t} dt = (e^{c·T} − 1)/c.

**Theorem 1.2 (exp n2T eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.exp_n2T_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.exp_n2T_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

With T = 16·log n/n², the exponent is exactly 2·log n, so e^{n²T/8} = n².

**Theorem 1.3 (integral exp n2 eq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_n2_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_n2_eq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The t-integral of Lemma 4.3's bound, exactly. ∫₀ᵀ e^{n²t/8} dt = 8 − 8/n². No asymptotics: this is an identity at T = 16·log n/n². Verified numerically against quadrature to ten digits (/private/tmp/claude-501/b-l10-2/t_integral.py).

**Theorem 1.4 (T nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.T_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.T_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

T = 16·log n/n² is non-negative for n ≥ 1.

**Theorem 1.5 (antitone integral).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.antitone_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.antitone_integral` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

An integral of antitone functions is antitone.

**Theorem 1.6 (integral nonneg of nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_nonneg_of_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_nonneg_of_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The t-integrated profile is non-negative.

**Theorem 1.7 (lintegral radial t swap).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_swap` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Tonelli for the radial/t pair. The ℝ≥0∞ swap; only measurability is needed.

**Theorem 1.8 (lintegral radial t le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The t-integrated radial bound in ℝ≥0∞. Feed the fixed-t Lemma 4.3 bound ∫ y ≤ C₁·e^{n²t/8} and get ∫ y ∫ t ≤ C₁·(8 − 8/n²) — the exact constant of §1.

**Theorem 1.9 (radial bound of lintegral).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.radial_bound_of_lintegral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.radial_bound_of_lintegral` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

From an ℝ≥0∞ bound to RadialWeightData.radial_bound. The Bochner statement the structure wants, recovered from the ℝ≥0∞ one under integrability.

**Theorem 1.10 (lintegral t of Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_t_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_t_ofReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Pulling y^{n−1} and the t-integral through ENNReal.ofReal.

**Theorem 1.11 (eight sub nonneg).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.eight_sub_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.eight_sub_nonneg` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

8 − 8/n² ≥ 0 for n ≥ 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.T_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.antitone_integral`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.eight_sub_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.exp_n2T_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_mul_Ioc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_exp_n2_eq`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.integral_nonneg_of_nonneg`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_radial_t_swap`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.lintegral_t_ofReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43C.radial_bound_of_lintegral`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B](Lemma43B.md)
