# GOETail2

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate goetail2 to the stochastic ellipsoid construction.

**Theorem 1.1 (has Subgaussian MGF of has Law gaussian Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_hasLaw_gaussianReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_hasLaw_gaussianReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A real random variable whose law is N(0, v) has a sub-Gaussian MGF with parameter v. Mathlib has mgf_gaussianReal and integrable_exp_mul_gaussianReal but no bridge to HasSubgaussianMGF, which occurs in no file other than Probability/Moments/SubGaussian.lean.

**Theorem 1.2 (has Subgaussian MGF of map gaussian Real).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_map_gaussianReal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_map_gaussianReal` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A nondegenerate Gaussian map equality also certifies a.e. measurability: a nonmeasurable map has zero pushforward, whereas every Gaussian law is a probability measure.

**Theorem 1.3 (dot Product mul Vec comm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.dotProduct_mulVec_comm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.dotProduct_mulVec_comm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The bilinear form of a symmetric matrix is symmetric.

**Theorem 1.4 (inner to Euclidean CLM symm).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_toEuclideanCLM_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_toEuclideanCLM_symm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

toEuclideanCLM of a symmetric real matrix is self-adjoint, in the elementary form D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.opNorm_le_of_net consumes.

**Theorem 1.5 (is Symm add transpose).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.isSymm_add_transpose`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.isSymm_add_transpose` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

B + Bᵀ is symmetric.

**Definition 1.6 (quad Form).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.quadForm`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.quadForm` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The quadratic form of the symmetrised matrix, as a linear form in the independent entries of B.

**Theorem 1.7 (inner symmetrized).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_symmetrized`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_symmetrized` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Step 3a. The quadratic form of B + Bᵀ is a sum over the *full* product Fin n × Fin n of the independent entries of B, with coefficients 2 x_i x_j. No i ≤ j filter and no Prod.swap reindexing: the only reindexing is one Finset.sum_comm.

**Theorem 1.8 (sum sq coord eq one).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.sum_sq_coord_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.sum_sq_coord_eq_one` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

A unit vector of EuclideanSpace ℝ (Fin n) has coordinate squares summing to 1.

**Theorem 1.9 (has Subgaussian MGF quad Form).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_quadForm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_quadForm` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Step 3c. For a unit vector x, the linear form ∑ p, (2 x_{p.1} x_{p.2}) B_{p.1 p.2} in the independent entries of B is sub-Gaussian with parameter 4c. The coefficient bound is D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.sum_sq_coeff_le; the closure properties are HasSubgaussianMGF.const_mul and .sum_of_iIndepFun, and the parameter is relaxed by D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.hasSubgaussianMGF_mono.

**Theorem 1.10 (op Norm Tail symmetrized).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.opNormTail_symmetrized`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.opNormTail_symmetrized` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The tail, with C = 12. Steps 4 (union bound over the ε = 1/4 net), 5 (the constant), 6 (assembly) and 8 (n = 0).

**Theorem 1.11 (gaussian op Norm Tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.gaussian_opNormTail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.gaussian_opNormTail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Gaussian case at a general variance, which is the form the discrete chain of hinge 1 plugs into: its increment after time t is a standard Gaussian on R^{n×n}_sym scaled by √t, i.e. B + Bᵀ with the entries of B i.i.d. N(0, t/4).

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.dotProduct_mulVec_comm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.gaussian_opNormTail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_hasLaw_gaussianReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_of_map_gaussianReal`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.hasSubgaussianMGF_quadForm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_symmetrized`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.inner_toEuclideanCLM_symm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.isSymm_add_transpose`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.opNormTail_symmetrized`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.quadForm`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2.sum_sq_coord_eq_one`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail](GOETail.md)
