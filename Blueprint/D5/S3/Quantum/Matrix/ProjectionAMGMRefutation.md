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

## The scalar200 basis counterexample

The dimension-three kernel-checked result above is the existing public refutation. The following complete scalar comparison is an existing-owner exposition of a separate private native-verified candidate; it adds no public declaration, freeze, deposit or second open-problem-resolution binding.

Fix n=200, K=1000000000 and s=sqrt(K^2+1). In the standard orthonormal basis e0,...,e199, take a0=e1, ai=(K e1+e(i+1))/s for 1<=i<=198, and a199=(e0-e1)/sqrt(2). Take z=e0+200e1. The submitted family is this finite real unit-column basis; the dependent auxiliary family below is only a comparison.

Every column has squared length one. The spanning identities e1=a0, e(i+1)=s ai-K a0 and e0=sqrt(2)a199+a0 recover every standard vector at the fixed positive finite K. Finite-dimensional spanning with 200 columns gives linear independence. Thus the witness is an actual basis in R^200, and each complement I-ai ai^T is a self-adjoint idempotent contraction.

For the auxiliary family, retain the last projection Q and replace the first 199 projections by P=I-e1 e1^T. The unique Q position occurs 199! times in the full labelled permutation sum. Therefore the complete 200! reversed-permutation average is (1/200) sum from k=0 to 199 of P^(199-k) Q P^k, equivalently (PQ+QP+198PQP)/200; no permutation terms are discarded or enumerated. On span(e0,e1), the mean is B=[[399,1],[1,1]]/400 and the product average is [[1/2,1/400],[1/400,0]], whose quadratic form at (1,200) is exactly 3/2.

The two-dimensional Euclidean operator norm of B is at most 401/402, by an exact positive quadratic-form estimate. The first three binomial terms give (402/401)^196 >= 258507/160801 > 8/5, hence (401/402)^196 < 5/8. Direct multiplication gives B^2(1,200)=(119601/80000,1/200), with squared length below 9/4. Symmetry and B^100=B^98 B^2 imply (1,200)^T B^200(1,200) < 45/32, so the auxiliary difference has quadratic form below -3/32.

Exactly 198 factors change. Each changed projection difference is supported on span(e1,e(i+1)); its matrix there is [[1,-K],[-K,-1]]/(K^2+1), whose square is the plane identity divided by K^2+1. Hence its norm is at most 1/s. Product telescoping for contractions bounds every original permutation word against its auxiliary word by 198/s, and the full uniform average has the same bound. The mean difference is at most 198/(200s); telescoping its 200th power gives 198/s. The two original AM-GM differences therefore differ in norm by at most 396/s < 396/K.

The squared length of z is 40001. Cauchy-Schwarz gives the strict original certificate z^T(M^200-G)z < -3/32 + 15840396/1000000000 < -1/16 < 0. This contradicts positive semidefiniteness and refutes the literal all-order scalar basis assertion at the even dimension n=200. The argument preserves the full-space estimates and the complete factorially weighted average.

For the source correspondence with a Hessian square-root convention, put C=A^T A and U=A C^(-1/2). Then U is orthogonal and A=U C^(1/2); all complement projections, means, powers and individual permutation words are carried by the same orthogonal conjugation, and U^T z has the identical negative form. This bridge does not assign a sign to the separate expected-inverse reformulation.

The private source snapshot is native-verified on Mac Studio under Lean 4.35 with no sorryAx in its scoped report and with the literal result type Not claimScalar; the source SHA-256 is 1067ac81d5cb1acca53faf795d906c6d832b55ab7c16c3890f44a6c143ca15ec. This paragraph records the proof and its evidence boundary without claiming that the unpublished candidate is a new admitted public declaration. The smallest failing dimension, the optimal random-permutation coordinate-descent rate, and the separate second-moment comparison remain open.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.meanProj`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.sixPerms_univ`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.symProd`
