# Lemma43B

## Abstract

Contact profile counts and accumulated projection dimension.

Contact profile counts and accumulated projection dimension. The results below relate lemma43b to the stochastic ellipsoid construction.

**Theorem 1.1 (mul exp neg le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.mul_exp_neg_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.mul_exp_neg_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

s·e^{-s} ≤ e⁻¹ for every real s. One application of 1 + x ≤ e^x at x = s - 1.

**Theorem 1.2 (sq mul exp le four).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.sq_mul_exp_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.sq_mul_exp_le_four` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

b²·e^{-b²/8} ≤ 4. This is what makes the near piece of the split integrate to ≤ 2/b.

**Theorem 1.3 (integral shifted gaussian).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.integral_shifted_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.integral_shifted_gaussian` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The total mass of the shifted Gaussian.

**Theorem 1.4 (norm le of mem cube).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.norm_le_of_mem_cube`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.norm_le_of_mem_cube` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Every point of the unit cube at y has norm within √n/2 of ‖y‖.

**Theorem 1.5 (dom of antitone).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.dom_of_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.dom_of_antitone` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Worst-point domination from antitonicity. With f r = g (r − √n/2) for an antitone g, the weight g ‖toE n y‖ is dominated by f ‖x‖ at *every* x in the cube at y.

**Definition 1.6 (subst).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The substitution y ↦ r = (a₀ − s·y)^{−1/2}, with s = √t.

**Definition 1.7 (subst Deriv).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.substDeriv`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.substDeriv` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Its derivative, s / (2·u^{3/2}) with u = a₀ − s·y.

**Theorem 1.8 (subst sq).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_sq` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

(a₀ − s·y) = 1/(subst a₀ s y)²: the substitution inverts r ↦ (a₀ − r^{−2})/s.

**Theorem 1.9 (strict Mono On subst).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.strictMonoOn_subst`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.strictMonoOn_subst` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The substitution is strictly increasing where it is defined (s > 0).

**Theorem 1.10 (subst integrand).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_integrand`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_integrand` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The substituted integrand. |φ'(y)|·φ(y)^{n−1} = (s/2)·(a₀ − s·y)^{−(n+2)/2} — the exponent (n+2)/2 of eq. (56), assembled from r^{n−1} and the Jacobian's u^{−3/2}.

**Theorem 1.11 (rpow neg le of one le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.rpow_neg_le_of_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.rpow_neg_le_of_one_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The a₀ ≥ 1 normalisation (p. 20): (a₀ − u)^{−c} ≤ (1 − u)^{−c}, which is how the substituted integrand (a₀ − s·y)^{−(n+2)/2} is handed to Lemma43.integrand_le, whose statement is normalised at a₀ = 1. The paper writes this as a₀^{−(n+2)/2} ≤ 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.dom_of_antitone`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.integral_shifted_gaussian`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.mul_exp_neg_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.norm_le_of_mem_cube`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.rpow_neg_le_of_one_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.sq_mul_exp_le_four`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.strictMonoOn_subst`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.substDeriv`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_integrand`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Contact/Lemma43B.subst_sq`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Construction/Section5](../Construction/Section5.md)
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/Lemma43](Lemma43.md)
