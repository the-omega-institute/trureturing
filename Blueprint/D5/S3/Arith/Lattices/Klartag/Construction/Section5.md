# Section5

## Abstract

Construction A lattices, covolumes and ellipsoid transfer.

Construction A lattices, covolumes and ellipsoid transfer. The results below relate section5 to the stochastic ellipsoid construction.

**Definition 1.1 (kappa).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.kappa`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Construction/Section5.kappa` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

κ_n = Vol_n(Bⁿ), as a real number.

**Theorem 1.2 (two lt exp three quarters).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_lt_exp_three_quarters`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_lt_exp_three_quarters` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

2 < exp (3/4), via exp (3/4) = exp (1/8) ^ 6 ≥ (9/8) ^ 6 = 531441/262144.

**Theorem 1.3 (two mul pow lt one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_pow_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_pow_lt_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Use-1 arithmetic core: x ≤ 1 - 1/n + δ with n·δ ≤ 1/4 forces 2·xⁿ < 1. This replaces Klartag's (1-1/n)ⁿ ≤ 1/e and is *stronger*: e^{-3/4} < 1/2, so the union bound gets 1/2 + 1/2 rather than 1/e + 1/2, with strictness to spare.

**Theorem 1.4 (two mul card lt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_lt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The integer-point count of a ball, in the form the union bound consumes.

**Theorem 1.5 (use one arith).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.use_one_arith`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.use_one_arith` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Use-1 volume condition, discharged. Under Klartag's normalisation αⁿ·m = κ_n (so that α·Λ(g) has covolume κ_n), a scaled radius α·(R + √n/2) ≤ 1 - 1/n + δ with n·δ ≤ 1/4 gives the hypothesis of two_mul_card_lt.

**Theorem 1.6 (two mul card bad one lt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_one_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_one_lt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Use 1 (eq. 64), discrete counterpart. Fewer than half of the pⁿ-1 lines meet the small ball at all.

**Theorem 1.7 (sum weight on Line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.sum_weight_onLine`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.sum_weight_onLine` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Weighted first-moment lemma. The same swap of two finite sums as ConstructionA.sum_card_filter_onLine, with weights — this is what eq. (65)'s K̃_t (a sum of Φ-values, not a bare count) actually needs.

**Theorem 1.8 (card bad two weighted le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.card_bad_two_weighted_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.card_bad_two_weighted_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Weighted Markov (eq. 66).

**Theorem 1.9 (two mul card bad two lt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_two_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_two_lt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Use 2 (eq. 66), discrete counterpart. Fewer than half of the lines carry a weighted contact sum of θ or more.

**Theorem 1.10 (weight bound of lintegral).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.weight_bound_of_lintegral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.weight_bound_of_lintegral` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

From an integral bound to ChainData.weight_bound. This is the connector between Lemma 4.3 (∫ Φ ≤ C₁κ_n e^{n²t/8}, evaluated by polar coordinates — the Mathlib entry point is MeasureTheory.Measure.integral_fun_norm_addHaar, Constructions/HaarToSphere.lean:296) and the finite Markov step. The domination hypothesis hdom is where radial monotonicity of Φ is used: on the cube at y, Φ at y is below Φ at the *inner* radius.

**Theorem 1.11 (exists good line).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Proposition 5.1 (Construction A form), weighted. 1/2 + 1/2 < 1: Use 1 kills fewer than half the lines, Use 2 kills fewer than half, so a line survives both.

**Theorem 1.12 (exists good line of chain Data).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line_of_chainData`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line_of_chainData` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

§5's output. A single Construction-A line g that is simultaneously lattice-free in the small ball (Klartag's eq. 64) and light in contacts (his eq. 66).

**Theorem 1.13 (red Mod ne zero of norm lt).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.redMod_ne_zero_of_norm_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.redMod_ne_zero_of_norm_lt` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

p-indivisibility from a norm bound, pointwise. This is the pointwise form of ConstructionA.redMod_ne_zero_of_abs_lt, and it is what discharges ChainData.ball_indivisible from R < p.

**Theorem 1.14 (exists prime alpha le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_prime_alpha_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_prime_alpha_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For every n ≥ 2 and every ε > 0 a prime p makes the Klartag scale α ≤ ε. α = (κ_n / p^{n-1})^{1/n} → 0 as p → ∞, and p appears nowhere in the conclusion.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.card_bad_two_weighted_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_good_line_of_chainData`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.exists_prime_alpha_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.kappa`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.redMod_ne_zero_of_norm_lt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.sum_weight_onLine`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_lt_exp_three_quarters`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_one_lt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_bad_two_lt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_card_lt`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.two_mul_pow_lt_one`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.use_one_arith`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Construction/Section5.weight_bound_of_lintegral`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA](ConstructionA.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Tiling](Tiling.md)
