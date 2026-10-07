# Gaussian Maximal3

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate gaussian maximal3 to the stochastic ellipsoid construction.

**Theorem 1.1 (exp one le 2d N).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.exp_one_le_2dN`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.exp_one_le_2dN` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

exp 1 ≤ 2·d·N. At n ≥ 3 the right side is at least 36.

**Definition 1.2 (c Adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.cAdopted`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.cAdopted` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The chain's adopted scale, c = √h with h = ParamsAdopted2.stepSizeAdopted2 n.

**Theorem 1.3 (maximal At Adopted adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.maximalAtAdopted_adopted`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.maximalAtAdopted_adopted` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

MaximalAtAdopted with no hypothesis but 3 ≤ n.

**Theorem 1.4 (integrable At Index adopted).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.integrableAtIndex_adopted`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.integrableAtIndex_adopted` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

IntegrableAtIndex with no hypothesis but 3 ≤ n.

**Theorem 1.5 (B adopted le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.B_adopted_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.B_adopted_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

B_adopted n ≤ 5·√(h·d)·√(log n) for n ≥ 2 073 600. The max is the first term because √(h·d)·(2·log K + 2) ≤ 28·n^{−2.5} < 1.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.B_adopted_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.cAdopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.exp_one_le_2dN`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.integrableAtIndex_adopted`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal3.maximalAtAdopted_adopted`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GaussianMaximal2](GaussianMaximal2.md)
