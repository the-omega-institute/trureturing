# Lemma43

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43 to the stochastic ellipsoid construction.

**Theorem 1.1 (neg log one sub le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_log_one_sub_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_log_one_sub_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The sharp bound. -log(1-x) ≤ x + x² for 0 ≤ x ≤ 1/2. This is the step that fixes the 1/8. The crude -log(1-x) ≤ 2x, also true on [0,1/2], would put γ = 1/2 and destroy the n².

**Theorem 1.2 (rpow one sub le exp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.rpow_one_sub_le_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.rpow_one_sub_le_exp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(1 - x)^{-m/2} ≤ exp((m/2)·(x + x²)) for 0 ≤ x ≤ 1/2 and 0 ≤ m.

**Theorem 1.3 (neg sq half add mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_sq_half_add_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_sq_half_add_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

-y²/2 + b·y = -(y-b)²/2 + b²/2.

**Theorem 1.4 (half sq drift).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.half_sq_drift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.half_sq_drift` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The 1/8. With drift b = n√t/2, the Legendre value is b²/2 = n²t/8.

**Theorem 1.5 (integrand le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.integrand_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.integrand_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Lemma 4.3's integrand, bounded, with the 1/8 explicit. For y > 0 with y√t ≤ 1/2, Φ(y)·(1 - y√t)^{-(n+2)/2} ≤ (e^J / (√(2π)·y)) · e^{n²t/8} · e^{-(y - n√t/2)²/2} where J bounds the junk y√t + ((n+2)/2)·(y√t)². On the paper's range (1 ≤ y ≤ log n, √t ≤ 5√(log n)/n) the junk is o(1), so J may be taken to be any fixed positive number for n past a threshold — but nothing here needs that: J is a hypothesis, so the statement has no n₀. The three ingredients are PaddedTail.Phi's 1/r branch, rpow_one_sub_le_exp (the sharp log bound), and neg_sq_half_add_mul + half_sq_drift (completing the square).

**Theorem 1.6 (lintegral radial le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.lintegral_radial_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.lintegral_radial_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The radial reduction. For a non-negative radial integrand, ∫⁻ x, ofReal (f ‖x‖) ≤ ofReal (n · κ_n · C) whenever the one-dimensional integral is ≤ C.

**Theorem 1.7 (weight bound of radial).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.weight_bound_of_radial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.weight_bound_of_radial` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

ChainData.weight_bound from a radial one-dimensional bound. This is the exact statement the interface consumes: give a non-negative radial profile f dominating the contact weight on each unit cube, an integrability certificate, and a bound C on ∫₀^∞ yⁿ⁻¹ f(y) dy; the Markov threshold field follows.

**Theorem 1.8 (one Dim le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.oneDim_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.oneDim_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

I₂ with e^{n²t/8} factored out. The remaining integral is Gaussian.

**Theorem 1.9 (prefactor cancel).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.prefactor_cancel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.prefactor_cancel` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The prefactor cancels. Eq. (56)'s prefactor is n√t/2 = b; the paper's Gaussian bound is K ≤ (2 + 2√(2π))/b. Their product is an absolute constant, with no n and no t left.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.half_sq_drift`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.integrand_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.lintegral_radial_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_log_one_sub_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.neg_sq_half_add_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.oneDim_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.prefactor_cancel`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.rpow_one_sub_le_exp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43.weight_bound_of_radial`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Section5](../Construction/Section5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail](../Tail/PaddedTail.md)
