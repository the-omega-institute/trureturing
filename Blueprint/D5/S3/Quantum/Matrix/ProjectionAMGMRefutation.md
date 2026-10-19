# Projection-matrix AM-GM refutation

## Abstract

A rank-one projection family gives a negative quadratic form for the matrix AM-GM difference.

**Definition 1.1 (The six permutations of three points).**

$$(sixPerms:Finset\left(\operatorname{Equiv.Perm}\left(Fin\left(3\right)\right)\right)) = \left\{1, \operatorname{Equiv.swap}\left((0:Fin\left(3\right)), 1\right), \operatorname{Equiv.swap}\left((0:Fin\left(3\right)), 2\right), \operatorname{Equiv.swap}\left((1:Fin\left(3\right)), 2\right), \operatorname{Equiv.swap}\left((0:Fin\left(3\right)), 1\right) \cdot \operatorname{Equiv.swap}\left((1:Fin\left(3\right)), 2\right), \operatorname{Equiv.swap}\left((1:Fin\left(3\right)), 2\right) \cdot \operatorname{Equiv.swap}\left((0:Fin\left(3\right)), 1\right)\right\}$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identity, the three transpositions, and the two products of adjacent transpositions list all permutations of Fin 3.

**Theorem 1.2 (The list contains every permutation).**

$$sixPerms = (\operatorname{Finset.univ}:Finset\left(\operatorname{Equiv.Perm}\left(Fin\left(3\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite set sixPerms equals the finite set of all permutations of Fin 3.

**Definition 1.3 (Arithmetic mean of projections).**

$$\forall (n:\mathbb{N}), \forall (N:\mathbb{N}), \forall (P:Fin\left(n\right)\to Matrix\left(Fin\left(N\right), Fin\left(N\right), \mathbb{R}\right)), meanProj\left(P\right) = \operatorname{Inv.inv}\left((n:\mathbb{R})\right)\cdot (\sum_{i:Fin\left(n\right)} P(i))$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.meanProj` (`✓ std3`).

*Citation.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Commentary.*

meanProj scales the finite sum of a projection family by the inverse of its cardinality.

**Definition 1.4 (Symmetrized projection product).**

$$\forall (n:\mathbb{N}), \forall (N:\mathbb{N}), \forall (P:Fin\left(n\right)\to Matrix\left(Fin\left(N\right), Fin\left(N\right), \mathbb{R}\right)), symProd\left(P\right) = \operatorname{Inv.inv}\left((\operatorname{Nat.factorial}\left(n\right):\mathbb{R})\right)\cdot (\sum_{sigma:\operatorname{Equiv.Perm}\left(Fin\left(n\right)\right)} \operatorname{List.prod}\left(\operatorname{List.reverse}\left(\operatorname{List.ofFn}\left(fun (k:Fin\left(n\right)) \mapsto P(sigma(k))\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.symProd` (`✓ std3`).

*Citation.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Commentary.*

symProd scales the sum over all permutation words by the inverse factorial; List.reverse makes the first permutation entry the rightmost factor.

**Definition 1.5 (Matrix AM-GM positive-semidefinite claim).**

$$(claim) \Leftrightarrow (\forall (n:\mathbb{N}), \forall (N:\mathbb{N}), \forall (P:Fin\left(n\right)\to Matrix\left(Fin\left(N\right), Fin\left(N\right), \mathbb{R}\right)), (1 \le n) \Rightarrow ((\forall (i:Fin\left(n\right)), (\operatorname{Matrix.transpose}\left(P(i)\right) = P(i)) \land (P(i) \cdot P(i) = P(i))) \Rightarrow (\operatorname{Matrix.PosSemidef}\left((meanProj\left(P\right))^{n} - symProd\left(P\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.claim` (`✓ std3`).

*Citation.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Commentary.*

Sun, Luo, and Ye state in Section 3.3: "We observe that we only need to prove a matrix AM-GM inequality for projection matrices. We conjecture that the following matrix AM-GM inequality holds. Conjecture (matrix AM-GM inequality for projection matrices). Suppose Pᵢ ∈ ℝᴺˣᴺ, i=1,…,n are projection matrices, then (1/n!) Σ_{σ=(σ₁,…,σₙ)∈Γ} P_{σₙ} P_{σₙ₋₁} ⋯ P_{σ₁} ⪯ ((1/n) Σᵢ Pᵢ)ⁿ." Here Γ is the set of all permutations of {1,…,n}, and X ⪯ Y means that Y−X is positive semidefinite. The displayed formula is its real finite-dimensional encoding.

**Theorem 1.6 (A negative quadratic form at dimension three).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sun-luo-ye-2020-projection-matrix-amgm` (refuted) by `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sun-luo-ye-2020-projection-matrix-amgm","declaration_gid":"D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Commentary.*

The explicit matrices on Fin 3 satisfy the projection hypotheses, but z=(1,1,1) gives zᵀ((meanProj P)^3−symProd P)z=−8/243. Positive semidefiniteness would force this quadratic form to be nonnegative, so the universal statement is false.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.meanProj`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms_univ`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.symProd`
