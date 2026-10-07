# Gaussian Fourth

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate gaussian fourth to the stochastic ellipsoid construction.

**Theorem 1.1 (pow four le exp).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_exp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_exp` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

y⁴ ≤ 24(e^y + e^{-y}). The i = 4 term of the exponential series at |y|.

**Theorem 1.2 (pow four le of pos).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_of_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_of_pos` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The domination that gives both the integrability and the moment bound.

**Theorem 1.3 (integral norm pow four le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.integral_norm_pow_four_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.integral_norm_pow_four_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

E[‖ξ_k‖⁴] ≤ 100·h²·d², h = c², d = Fintype.card (UT n). Chebyshev's sum inequality replaces the cross terms, so no independence of the coordinates is needed.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.integral_norm_pow_four_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_exp`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianFourth.pow_four_le_of_pos`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Drift/LogDetMartingale](../Drift/LogDetMartingale.md)
