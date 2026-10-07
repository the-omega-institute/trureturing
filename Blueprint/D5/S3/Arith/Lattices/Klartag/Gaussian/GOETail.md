# GOETail

## Abstract

Gaussian moments, independence and operator norm tails.

Gaussian moments, independence and operator norm tails. The results below relate goetail to the stochastic ellipsoid construction.

**Definition 1.1 (Is Separated).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.IsSeparated`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.IsSeparated` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

IsSeparated ε N : N is a finite set of unit vectors, any two distinct ones at distance more than ε. Note that Mathlib has an unrelated Metric.IsSeparated; this one is D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.IsSeparated and shadows it inside this namespace only.

**Theorem 1.2 (card le of is Separated).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.card_le_of_isSeparated`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.card_le_of_isSeparated` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Packing count. An ε-separated set of unit vectors has at most (1 + 2/ε) ^ d elements, d = finrank ℝ E. The proof is the volume argument: the balls of radius ε/2 around the points are pairwise disjoint and contained in the ball of radius 1 + ε/2.

**Theorem 1.3 (exists net).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.exists_net`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.exists_net` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Existence of an ε-net of the unit sphere with an explicit cardinality bound. A maximal ε-separated set of unit vectors is an ε-net, and the packing count bounds its size. Existence of a maximal one is Nat.sSup_mem: the set of achievable cardinalities is a nonempty set of naturals bounded above by the packing count.

**Theorem 1.4 (op Norm le of quadratic).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_quadratic` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For a self-adjoint continuous linear map on a real inner product space, the operator norm is bounded by any bound on the quadratic form over the unit sphere. This is the classical polarization argument, proved here self-containedly. Mathlib carries the same fact in the form ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (‖T‖ = ⨆ x, |T.rayleighQuotient x| for a symmetric T), built on ContinuousLinearMap.opNorm_le_of_re_inner_le; deriving this statement from those is the shorter route.

**Theorem 1.5 (op Norm le of net).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_net`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_net` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The net bound (Vershynin, *High-Dimensional Probability*, Lemma 4.4.1, symmetric case). If the quadratic form of a self-adjoint T is bounded by M on an ε-net of the unit sphere, then (1 - 2ε) * ‖T‖ ≤ M.

**Theorem 1.6 (sum sq coeff le).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.sum_sq_coeff_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.sum_sq_coeff_le` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

For a unit vector x, the coefficients 2 x i x j of the quadratic form ⟪A x, x⟫ in the independent entries A i j have squares summing to at most 4. This is the variance-proxy computation of step (3) of the outline; the sum is over all pairs, which dominates the sum over i ≤ j, so the same bound serves after restriction.

**Theorem 1.7 (union bound arith).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.union_bound_arith`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.union_bound_arith` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The numeric step of the union bound (step (5) of the outline): with an ε = 1/4 net of at most 9 ^ n unit vectors and the Chernoff exponent -(9/2) s² n obtained at u = 6 √c · s · √n, the union bound is dominated by exp (-s² n) for every s ≥ 1. Only Real.log 9 ≤ 3 is needed, so the constant has ample slack.

**Theorem 1.8 (has Subgaussian MGF mono).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.hasSubgaussianMGF_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.hasSubgaussianMGF_mono` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Monotonicity of the sub-Gaussian parameter. Mathlib has HasSubgaussianMGF.const_mul, .neg, .add_of_indepFun and .sum_of_iIndepFun, but no monotonicity lemma at pin 6f1ef4e5; step (3) of the outline needs one to replace ∑ p, c p by a uniform bound.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.IsSeparated`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.card_le_of_isSeparated`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.exists_net`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.hasSubgaussianMGF_mono`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_net`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.opNorm_le_of_quadratic`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.sum_sq_coeff_le`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail.union_bound_arith`
