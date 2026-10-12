# Rico–Życzkowski nonlinear monotone refutation

## Abstract

A three-outcome measurement on a two-dimensional complex space refutes the nonlinear 2-norm prefix inequality under commuting blockwise bistochastic dynamics.

**Definition 1.1 (Blockwise bistochastic matrices).**

$$\forall (n : \mathbb{N}), \forall (d : \mathbb{N}), \forall (B : \operatorname{Fin}(n) \to \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \operatorname{BlockBistoch}(B) = ((2 \le d) \land (\forall (i : \operatorname{Fin}(n)), \forall (j : \operatorname{Fin}(n)), (B(i, j)).\operatorname{PosSemidef}) \land (\forall (i : \operatorname{Fin}(n)), \sum_{j : \operatorname{Fin}(n)} B(i, j) = ((1 : \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})))) \land (\forall (j : \operatorname{Fin}(n)), \sum_{i : \operatorname{Fin}(n)} B(i, j) = ((1 : \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.BlockBistoch` (`✓ std3`).

*Citation.* Albert Rico; Karol Życzkowski (2024). *Discrete dynamics in the set of quantum measurements*. DOI: [10.1088/1751-8121/ad7dc2](https://doi.org/10.1088/1751-8121/ad7dc2). URL: <https://arxiv.org/abs/2308.05835v2>.

*Commentary.*

Definition 5, p. 12, verbatim (equations rendered inline): Let B be a square matrix of size dn × dn composed of n² blocks B_ij of size d × d each. We call B blockwise bistochastic if (i) its entries B_ij are positive semidefinite matrices of size d ≥ 2 (ii) its blockwise columns and rows sum to identity, Σ_i B_ij = Σ_j B_ij = 1_d. BlockBistoch includes the dimension condition 2 ≤ d, positivity and both identity resolutions.

**Definition 1.2 (The blockwise product).**

$$\forall (n : \mathbb{N}), \forall (d : \mathbb{N}), \forall (B : \operatorname{Fin}(n) \to \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \forall (P : \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \forall (Q : \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \operatorname{IsBlockProduct}(B, P, Q) = (\forall (i : \operatorname{Fin}(n)), Q(i) = (\sum_{j : \operatorname{Fin}(n)} \operatorname{CFC}.\operatorname{sqrt}(P(j)) * B(i, j) * \operatorname{CFC}.\operatorname{sqrt}(P(j))))$$

*Formalization.* `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.IsBlockProduct` (`✓ std3`).

*Citation.* Albert Rico; Karol Życzkowski (2024). *Discrete dynamics in the set of quantum measurements*. DOI: [10.1088/1751-8121/ad7dc2](https://doi.org/10.1088/1751-8121/ad7dc2). URL: <https://arxiv.org/abs/2308.05835v2>.

*Commentary.*

Definition 3 and Eq. (19), p. 8, verbatim (equation rendered inline): Let A and B be two matrices A = (A_ij) ∈ C^{dn} × C^{dn′} and B = (B_ij) ∈ C^{dn′} × C^{dn′′} composed of n × n′ and n′ × n′′ positive semidefinite blocks of size d, A_ij, B_ij ∈ C^d × C^d. We define the blockwise product, (A ∗ B)_ik = Σ_j √B_jk A_ij √B_jk ∈ C^{dn} × C^{dn′′}. For a probability column P the product is Q_i = Σ_j √P_j B_ij √P_j. CFC.sqrt is the principal positive semidefinite matrix square root, given by the continuous functional calculus for Hermitian matrices.

**Definition 1.3 (The 2-norm).**

$$\forall (d : \mathbb{N}), \forall (A : \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \operatorname{hs}(A) = (\sqrt{\operatorname{Complex}.\operatorname{re}(\operatorname{Matrix}.\operatorname{trace}(\operatorname{Matrix}.\operatorname{conjTranspose}(A) * A))})$$

*Formalization.* `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.hs` (`✓ std3`).

*Citation.* Albert Rico; Karol Życzkowski (2024). *Discrete dynamics in the set of quantum measurements*. DOI: [10.1088/1751-8121/ad7dc2](https://doi.org/10.1088/1751-8121/ad7dc2). URL: <https://arxiv.org/abs/2308.05835v2>.

*Commentary.*

Appendix C.1, p. 28, verbatim: where ‖A‖₂ = √tr[A†A] is the 2-norm. Matrix.conjTranspose is the conjugate transpose A†. The trace of Aᴴ A is real and nonnegative, so hs is the square root of its real part, the source's Hilbert–Schmidt 2-norm.

**Definition 1.4 (Conjecture 1).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), \forall (d : \mathbb{N}), \forall (P : \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \forall (Q : \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), \forall (B : \operatorname{Fin}(n) \to \operatorname{Fin}(n) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{ConcealmentKernelNecessityRefutation}.\operatorname{IsPOVM}(P)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{QuantumChannels}.\operatorname{ConcealmentKernelNecessityRefutation}.\operatorname{IsPOVM}(Q)) \Rightarrow (\operatorname{BlockBistoch}(B)) \Rightarrow (\operatorname{IsBlockProduct}(B, P, Q)) \Rightarrow \forall (\sigma : \operatorname{Equiv}.\operatorname{Perm}(\operatorname{Fin}(n))), \exists (\pi : \operatorname{Equiv}.\operatorname{Perm}(\operatorname{Fin}(n))), \forall (k : \mathbb{N}), (1 \le k) \Rightarrow (k \le n) \Rightarrow \operatorname{hs}(\sum_{i : \operatorname{Fin}(n), \operatorname{val}(i) < k} (P(\pi(i)) - (1 / (n : \mathbb{C}) : \mathbb{C}) \cdot (1 : \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})))) \ge \operatorname{hs}(\sum_{i : \operatorname{Fin}(n), \operatorname{val}(i) < k} (Q(\sigma(i)) - (1 / (n : \mathbb{C}) : \mathbb{C}) \cdot (1 : \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})))))$$

*Formalization.* `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.claim` (`✓ std3`).

*Citation.* Albert Rico; Karol Życzkowski (2024). *Discrete dynamics in the set of quantum measurements*. DOI: [10.1088/1751-8121/ad7dc2](https://doi.org/10.1088/1751-8121/ad7dc2). URL: <https://arxiv.org/abs/2308.05835v2>.

*Commentary.*

Appendix C.1, Conjecture 1, p. 28, verbatim: Let P ∈ Δ_{n,d} and Q ∈ Δ_{n,d} be blockwise probability vectors. If there exists a blockwise bistochastsic matrix B ∈ B_{n,d} such that Q = B ∗ P, then for any ordering of {Q_i} there exists an ordering of {P_i} such that ‖Σ_{i=1}^{k}(P_i − 1/n)‖₂ ≥ ‖Σ_{i=1}^{k}(Q_i − 1/n)‖₂ for all 1 ≤ k ≤ n, where ‖A‖₂ = √tr[A†A] is the 2-norm. Definition 1, p. 4, verbatim (equations rendered inline): A blockwise probability vector is a column vector P = (P_1, …, P_n)^T, with n components P_j being Hermitian, positive semidefinite matrices of order d, P_j ≥ 0, satisfying the identity resolution Σ_{j=1}^n P_j = 1_d. IsPOVM is D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM, specialized to Ω = Fin n. Matrix.PosSemidef includes Hermitian symmetry; 1 is the identity matrix. Lean uses zero-based Fin indices. The orderings σ and π are permutations of Fin n. Positions with i.val < k are exactly the first k positions; the range is 1 ≤ k ≤ n. Each occurrence of 1/n multiplies the d-dimensional identity matrix, with n cast to ℂ. The displayed formula compares 2-norms. BlockBistoch contains the source’s dimension restriction d ≥ 2. A centered dot between a complex scalar and a matrix denotes Lean’s scalar action •.

**Theorem 1.5 (Refutation at n = 3, d = 2).**

$$\neg\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rico-zyczkowski-2024-nonlinear-majorization-monotone` (refuted) by `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rico-zyczkowski-2024-nonlinear-majorization-monotone","declaration_gid":"D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Albert Rico; Karol Życzkowski (2024). *Discrete dynamics in the set of quantum measurements*. DOI: [10.1088/1751-8121/ad7dc2](https://doi.org/10.1088/1751-8121/ad7dc2). URL: <https://arxiv.org/abs/2308.05835v2>.

*Commentary.*

Take P₀ = diag(5/12, 1/6), P₁ = diag(1/6, 5/12), and P₂ = diag(5/12, 5/12). On the first diagonal coordinate, interchange outcomes 0 and 1; on the second, keep them fixed. Mix each of these permutations with the uniform three-outcome matrix using weights 9/10 and 1/10. All blocks are diagonal and positive semidefinite, and every block row and column sums to the identity. The principal positive semidefinite square roots give Q₀ = diag(11/60, 11/60) and Q₁ = Q₂ = diag(49/120, 49/120). The squared 2-norm values satisfy hs(P_j − (1/3) • 1)² ≤ 5/144 for every j and hs(Q₀ − (1/3) • 1)² = 9/200 > 5/144. Monotonicity of the square root makes k = 1 fail for every input ordering when the output ordering is the identity.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.BlockBistoch`
- Truth anchor: `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.IsBlockProduct`
- Truth anchor: `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.hs`
- Truth anchor: `D5/S3/Quantum/Measurements/RicoZyczkowskiMonotoneRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
