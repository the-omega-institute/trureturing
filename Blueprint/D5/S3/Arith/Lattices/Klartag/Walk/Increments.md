# Increments

## Abstract

Gaussian matrix walk, filtration and stopped increments.

Gaussian matrix walk, filtration and stopped increments. The results below relate increments to the stochastic ellipsoid construction.

**Theorem 1.1 (map std Gaussian isometry).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_stdGaussian_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_stdGaussian_isometry` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Rotational invariance. The standard Gaussian on a finite-dimensional real inner product space is invariant under every linear isometry equivalence. This is the one-line replacement for the use of Lévy's characterisation in Klartag's Lemma 3.1.

**Theorem 1.2 (char Fun map of inner).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.charFun_map_of_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.charFun_map_of_inner` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The characteristic function of a pushforward, when the map has an explicit "adjoint". Stated without ContinuousLinearMap.adjoint so that no CompleteSpace hypothesis is needed and the formula can be used for maps into a different space.

**Definition 1.3 (UT).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.UT`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.UT` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The upper triangle, including the diagonal: the index set of the coordinates of a symmetric matrix.

**Definition 1.4 (up).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.up`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.up` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The sorted pair (min i j, max i j).

**Definition 1.5 (cc).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.cc`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.cc` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The coordinate weight: 1 on the diagonal, 1/√2 off it. These are the coefficients that make symMat a Frobenius isometry.

**Definition 1.6 (sym Mat).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.symMat`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.symMat` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The symmetric matrix with the given Frobenius coordinates.

**Theorem 1.7 (fiber up).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.fiber_up`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.fiber_up` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The fibre of the sorting map over p is the (possibly degenerate) pair {(a,b), (b,a)}.

**Theorem 1.8 (sum sym Mat mul).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.sum_symMat_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.sum_symMat_mul` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

symMat is a Frobenius isometry. This is what justifies modelling R^{n×n}_sym by EuclideanSpace ℝ (UT n): the Euclidean inner product of the coordinates is the Frobenius inner product ∑_{i,j} A_ij B_ij of the matrices.

**Definition 1.9 (mk Mat).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkMat`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkMat` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The symmetric matrix with prescribed upper-triangular entries.

**Definition 1.10 (mk CLM).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkCLM`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkCLM` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

mkMat followed by Matrix.toEuclideanCLM, bundled as a linear map so that its continuity is LinearMap.continuous_of_finiteDimensional.

**Definition 1.11 (coord Vec).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.coordVec`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.coordVec` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The Frobenius coordinates of the scaled symmetric Gaussian matrix.

**Definition 1.12 (Aux).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.Aux`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.Aux` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The auxiliary probability space carrying a matrix with i.i.d. entries: a product indexed by the upper triangle and then by the two independent slots B a b and B b a.

**Definition 1.13 (aux B).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The matrix with i.i.d. entries.

**Definition 1.14 (e Idx).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.eIdx`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.eIdx` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The index map (i,j) ↦ (sorted pair, slot); it is injective, which is why the entries of auxB are independent over the full product.

**Theorem 1.15 (aux B indep).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_indep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_indep` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The first hypothesis D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail consumes: the entries of auxB are independent over the full product Fin n × Fin n.

**Theorem 1.16 (aux B law).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_law`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_law` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The second hypothesis D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail consumes: every entry of auxB is N(0, v).

**Definition 1.17 (phi).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.phi`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.phi` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The block map producing the symmetrised entry from the two independent slots.

**Definition 1.18 (v Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.vOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.vOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

v = r²/4: the entry variance of the i.i.d. matrix that matches the scaling r of the symmetric Gaussian.

**Definition 1.19 (var Of).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.varOf`

*Formalization.* `D5/S3/Arith/Lattices/Klartag/Walk/Increments.varOf` (`✓ std3`).

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The variance of the symmetrised entry at p: r² on the diagonal, r²/2 off it — Klartag's E Γ_ij ^ 2 = (1 + δ_ij)/n after the scaling r = √(2/n).

**Theorem 1.20 (map coord Vec eq map aux V).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_coordVec_eq_map_auxV`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_coordVec_eq_map_auxV` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

The law of the symmetric Gaussian matrix is the law of B + Bᵀ with i.i.d. B. This is Lemma 3.1's output in discrete form: it is what lets D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail, whose matrix is B + Bᵀ with independent entries over the full product, be applied to the chain's increment, whose entries above and below the diagonal are *equal* and therefore not independent.

**Theorem 1.21 (increment op Norm tail).**

Lean statement: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.increment_opNorm_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Klartag/Walk/Increments.increment_opNorm_tail` (`✓ std3`). ∎

*Citation.* Boaz Klartag (2025). *Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid*. DOI: [10.48550/arXiv.2504.05042](https://doi.org/10.48550/arXiv.2504.05042). URL: <https://arxiv.org/abs/2504.05042>.

*Commentary.*

Klartag, Corollary 3.2, for the discrete chain's increment. If ξ is a standard Gaussian on the model EuclideanSpace ℝ (UT n) of R^{n×n}_sym, then the symmetric matrix r · symMat ξ — which is the increment of the Dyson walk after time r², E (W_t)_ij² = t (1 + δ_ij)/2 — satisfies, for every s ≥ 1, P(‖r · symMat ξ‖_op ≥ 6 r s √n) ≤ 4 exp (-s² n). The proof runs D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail on the auxiliary i.i.d. space and transports the conclusion along map_coordVec_eq_map_auxV.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.Aux`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.UT`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_indep`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.auxB_law`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.cc`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.charFun_map_of_inner`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.coordVec`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.eIdx`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.fiber_up`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.increment_opNorm_tail`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_coordVec_eq_map_auxV`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.map_stdGaussian_isometry`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkCLM`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.mkMat`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.phi`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.sum_symMat_mul`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.symMat`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.up`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.vOf`
- Truth anchor: `D5/S3/Arith/Lattices/Klartag/Walk/Increments.varOf`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Gaussian/GOETail2](../Gaussian/GOETail2.md)
