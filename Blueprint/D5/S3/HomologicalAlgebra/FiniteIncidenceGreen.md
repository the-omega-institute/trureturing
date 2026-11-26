# Finite Incidence Green Series and Integral Repair

## Abstract

Two Green series give incidence-volume bounds for finite real unit repairs. Total unimodularity transfers the smaller applicable bound to a common integral and modular repair.

Let A be a finite real edge-to-face matrix and let a nonzero entry define an adjacency. The Euclidean coordinate spaces use the usual edge and face bases. For a signed simplicial coboundary these are the simplex bases. The real series require the chosen face unit to belong to the real image of A.

**Definition 1.1 (Face ball).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceBall`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceBall` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Start at the face f. Each round retains previous faces and adds all faces that share an incident edge with them. After j rounds the face radius is 2j.

**Definition 1.2 (Edge ball).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.edgeBall`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.edgeBall` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Take the edges incident to the j-th face ball. The edge radius is 2j+1. Write V_f(j) for the number of edges in this ball.

**Definition 1.3 (Euclidean incidence operator).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.incidence`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The real matrix acts as a continuous linear map from edge coordinates to face coordinates.

**Definition 1.4 (Neumann residual).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Use Q = I − AAᵀ/M² on face space.

**Definition 1.5 (Face unit).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceUnit`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceUnit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The Euclidean coordinate vector has value one at f and zero elsewhere.

**Theorem 1.6 (Propagation through the face Laplacian).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_pow_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_pow_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The j-th residual power applied to the unit vanishes outside the j-th face ball. Each application of AAᵀ connects only faces sharing an edge.

**Theorem 1.7 (Propagation to edges).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.transpose_residual_pow_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.transpose_residual_pow_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The transpose extends the support of the j-th residual power by one incidence step, so the resulting edge vector vanishes outside the j-th edge ball.

**Definition 1.8 (Neumann term).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannTerm`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Apply Q to power j to the face unit, apply the transpose, and scale by the inverse of M².

**Definition 1.9 (Neumann volume weight).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannWeight`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The degree-j majorant is sqrt(V_f(j)) q^j / M.

**Theorem 1.10 (Real Neumann repair and tail).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_repair`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Assume 0 < M, 0 ≤ q < 1, operator norm at most M, and residual contraction by q on the image. For a face unit in that image the Neumann terms sum to a solution. The sum of the volume weights bounds its L1 cost. Outside the ball of index J the bound uses the terms of degree J+1 and higher.

**Theorem 1.11 (Integral transfer of the Neumann bound).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_integer_and_zmod_repair`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_integer_and_zmod_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

For the real scalar extension of a totally unimodular integer incidence matrix, the same assumptions give an integer solution with L1 cost bounded by the Neumann volume sum. The reduction of this integer solution solves the equation over every ZMod n with support bounded by that sum.

**Definition 1.12 (Face Laplacian on the image).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.laplacianOnRange`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.laplacianOnRange` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Restrict AAᵀ to the real image of A.

**Theorem 1.13 (Neumann contraction from a spectral gap).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_contracts_of_spectral_gap`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_contracts_of_spectral_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Assume 0 < σ ≤ M, operator norm at most M, and lower bound σ² for positive eigenvalues of AAᵀ on the real image. The residual contracts there by q = 1 − σ²/M².

**Definition 1.14 (Chebyshev term).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Center and scale the face Laplacian on the interval [σ², M²]. Apply the degree-j Chebyshev iterate to the face unit, then the transpose and the corresponding reciprocal-series coefficient. The coefficient uses signed rate (σ − M)/(M + σ) and multiplicity one at zero and two thereafter.

**Theorem 1.15 (Chebyshev propagation to edges).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

The three-term recurrence gives the same edge radius 2j+1 at degree j.

**Definition 1.16 (Chebyshev volume weight).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevWeight`

*Formalization.* `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

For ρ = (M − σ)/(M + σ), the majorant is sqrt(V_f(0))/σ at degree zero and 2 sqrt(V_f(j)) ρ^j / σ at positive degrees.

**Theorem 1.17 (Real Chebyshev repair and tail).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshev_repair`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshev_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Assume 0 < σ < M, operator norm at most M, and the positive eigenvalue bound σ² on the restricted face Laplacian. For a face unit in the image the series sums to a solution with L1 cost bounded by the Chebyshev volume sum. The tail outside the J-th ball uses degrees J+1 and higher. The proof sums the scalar reciprocal series on the spectral interval and applies it in an eigenbasis of the image.

**Theorem 1.18 (One integral repair for both Green bounds).**

Lean statement: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.spectral_integer_and_zmod_repair`

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.spectral_integer_and_zmod_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoye Jiang, Lek-Heng Lim, Yuan Yao, Yinyu Ye (2011). *Statistical ranking and combinatorial Hodge theory*. DOI: [10.1007/s10107-010-0419-x](https://doi.org/10.1007/s10107-010-0419-x). URL: <https://arxiv.org/abs/0811.1067>.

*Commentary.*

Assume total unimodularity of the integer matrix, real feasibility of the face unit, 0 < σ ≤ M, real operator norm at most M, and lower bound σ² for the positive eigenvalues of the edge Laplacian AᵀA. Positive eigenvalues on the restricted face Laplacian transfer to the edge Laplacian. Choose the real repair with the smaller applicable volume bound and apply integral L1 repair to it.

The integer support is bounded by the integer L1 cost. That cost and every modular support are bounded by the minimum of the two volume sums when σ < M and by the Neumann sum when σ = M. Every reduction uses the same integer witness. The outside-ball tail estimates concern the real series.

Jiang, Lim, Yao and Ye provide combinatorial Hodge background. The polynomial approximation and sparse propagation mechanism belongs to the classical inverse-decay and matrix-function literature, including Demko, Moss and Smith, Decay Rates for Inverses of Band Matrices (1984), and Benzi and Razouk, Decay Bounds and O(n) Algorithms for Approximating Functions of Sparse Matrices (2007). The incidence-volume estimates and their application of the repository's integral repair theorem are derived here.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevTerm_vanishes`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshevWeight`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.chebyshev_repair`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.edgeBall`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceBall`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.faceUnit`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.incidence`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.laplacianOnRange`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannTerm`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumannWeight`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_integer_and_zmod_repair`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.neumann_repair`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_contracts_of_spectral_gap`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.residual_pow_vanishes`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.spectral_integer_and_zmod_repair`
- Truth anchor: `D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.transpose_residual_pow_vanishes`
- Dependency: [D5/S3/HomologicalAlgebra/TotalUnimodularL1Repair](TotalUnimodularL1Repair.md)
