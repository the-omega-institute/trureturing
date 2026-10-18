# Schmidt-number bounds for incomplete equiangular measurements

## Abstract

Equiangular measurements obey the Schmidt-number correlation trace-norm bound of Tavakoli and Morelli's Conjecture 2.

All matrices have complex entries. Ket(I) is the record of a vector v : I → ℂ and the normalization equation Σ_i ‖v(i)‖² = 1; u.vec denotes the underlying vector. The trace norm is the real trace of the positive square root of X adjoint times X, equivalently the sum of singular values. Natural indices are cast into the indicated scalar field before scalar arithmetic.

**Definition 1.1 (Local operators).**

$$\forall (d: \mathbb{N}), \operatorname{Op}\left(d\right) = \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.Op` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Op(d) is the space of square operators on a d-dimensional local system.

**Definition 1.2 (Bipartite operators).**

$$\forall (d: \mathbb{N}), \operatorname{BipartiteOp}\left(d\right) = \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.BipartiteOp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The product index represents two local systems of the same dimension d.

**Definition 1.3 (The pure-state projector).**

$$\forall (I: Type*), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall (u: \operatorname{Ket}\left(I\right)), \operatorname{proj}\left(u\right) = \operatorname{vecMulVec}\left((u).vec, \operatorname{star}\left((u).vec\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

A normalized ket determines the rank-one density matrix with entries u_i times the conjugate of u_j. The outer product is the underlying matrix of its pure state.

**Definition 1.4 (The coefficient matrix of a bipartite ket).**

$$\forall (d: \mathbb{N}), \forall (u: \operatorname{Ket}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), \operatorname{coeff}\left(u\right) = ((i: \operatorname{Fin}\left(d\right)) \mapsto ((j: \operatorname{Fin}\left(d\right)) \mapsto (u).vec\left((i, j)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Reshaping the coordinates of a bipartite ket gives its coefficient matrix. Its rank is the Schmidt rank, and its singular values are the Schmidt coefficients.

**Definition 1.5 (Schmidt number at most r).**

$$\forall (d: \mathbb{N}), \forall (rho: \operatorname{BipartiteOp}\left(d\right)), \forall (r: \mathbb{N}), (\operatorname{SchmidtNumberLE}\left(rho, r\right)) \Leftrightarrow (\exists (N: \mathbb{N}), \exists (p: (\operatorname{Fin}\left(N\right) \to \mathbb{R})), \exists (u: (\operatorname{Fin}\left(N\right) \to \operatorname{Ket}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right))), (\forall (k: \operatorname{Fin}\left(N\right)), 0 \le p\left(k\right)) \land ((\sum_{k: \operatorname{Fin}\left(N\right)} (p\left(k\right)) = 1) \land ((\forall (k: \operatorname{Fin}\left(N\right)), \operatorname{rank}\left(\operatorname{coeff}\left(u\left(k\right)\right)\right) \le r) \land (rho = \sum_{k: \operatorname{Fin}\left(N\right)} (\operatorname{smul}\left((p\left(k\right): \mathbb{C}), \operatorname{proj}\left(u\left(k\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.SchmidtNumberLE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Section II A defines the Schmidt number as the least positive r for which a state is a convex mixture of pure states of Schmidt rank at most r. This predicate expresses the at-most-r condition by a finite ensemble of normalized kets. The weights are nonnegative real numbers summing to one; each coefficient matrix has rank at most r. Positivity and trace one follow from the ensemble representation.

**Definition 1.6 (The table of joint probabilities).**

$$\forall (d: \mathbb{N}), \forall (I: Type*), [\operatorname{Fintype}\left(I\right)] \forall (rho: \operatorname{BipartiteOp}\left(d\right)), \forall (A: (I \to \operatorname{Op}\left(d\right))), \forall (B: (I \to \operatorname{Op}\left(d\right))), \operatorname{correlation}\left(rho, A, B\right) = ((a: I) \mapsto ((b: I) \mapsto (\operatorname{re}\left(\operatorname{trace}\left(rho \cdot \operatorname{kronecker}\left(A\left(a\right), B\left(b\right)\right)\right)\right): \mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.correlation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Equation (8) uses Born's rule for the joint outcome table of two local measurements. Here the entry is the real part of the trace of rho times the tensor product of the two effects, embedded into the complex numbers. The definition accepts arbitrary input matrices and finite operator families. For states and positive effects these entries are the joint probabilities.

**Definition 1.7 (The second moment of trace coordinates).**

$$\forall (d: \mathbb{N}), \forall (I: Type*), [\operatorname{Fintype}\left(I\right)] \forall (A: (I \to \operatorname{Op}\left(d\right))), \forall (H: \operatorname{Op}\left(d\right)), \operatorname{moment}\left(A, H\right) = \sum_{a: I} ((\operatorname{re}\left(\operatorname{trace}\left(H \cdot A\left(a\right)\right)\right))^{2})$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.moment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The moment sums the squared real trace coordinates of H against a finite operator family. No Hermitian hypothesis is imposed in this definition.

**Definition 1.8 (Nonnegative multiples of pure projectors).**

$$\forall (d: \mathbb{N}), \forall (A: \operatorname{Op}\left(d\right)), (\operatorname{ScaledPure}\left(A\right)) \Leftrightarrow (\exists (c: \mathbb{R}), \exists (u: \operatorname{Ket}\left(\operatorname{Fin}\left(d\right)\right)), (0 \le c) \land (A = \operatorname{smul}\left((c: \mathbb{C}), \operatorname{proj}\left(u\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.ScaledPure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

An operator is ScaledPure when it is a nonnegative real multiple of a normalized pure-state projector. The scalar zero is allowed.

**Definition 1.9 (A uniform second-moment bound).**

$$\forall (d: \mathbb{N}), \forall (I: Type*), [\operatorname{Fintype}\left(I\right)] \forall (A: (I \to \operatorname{Op}\left(d\right))), \forall (alpha: \mathbb{R}), \forall (beta: \mathbb{R}), (\operatorname{MomentBound}\left(A, alpha, beta\right)) \Leftrightarrow (\forall (H: \operatorname{Op}\left(d\right)), (\operatorname{IsHermitian}\left(H\right)) \Rightarrow (\operatorname{moment}\left(A, H\right) \le alpha \cdot \operatorname{re}\left(\operatorname{trace}\left(H \cdot H\right)\right) + beta \cdot (\operatorname{re}\left(\operatorname{trace}\left(H\right)\right))^{2}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.MomentBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For every Hermitian input, the moment is bounded by alpha times the real quadratic trace plus beta times the square of the real trace. Alpha and beta are arbitrary real parameters in this definition.

**Definition 1.10 (Equiangular measurements).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \operatorname{EAM}\left(d, n\right) = \{u: (\operatorname{Fin}\left(n\right) \to \operatorname{Ket}\left(\operatorname{Fin}\left(d\right)\right)) \mid (d < n) \land ((\sum_{a: \operatorname{Fin}\left(n\right)} (\operatorname{proj}\left(u\left(a\right)\right)) = \operatorname{smul}\left(\frac{(n: \mathbb{C})}{(d: \mathbb{C})}, (1: \operatorname{Op}\left(d\right))\right)) \land (\forall (a: \operatorname{Fin}\left(n\right)), \forall (b: \operatorname{Fin}\left(n\right)), (a \ne b) \Rightarrow ((\left\lVert \operatorname{dotProduct}\left(\operatorname{star}\left((u\left(a\right)).vec\right), (u\left(b\right)).vec\right) \right\rVert)^{2} = \frac{(n: \mathbb{R}) - (d: \mathbb{R})}{(d: \mathbb{R}) \cdot ((n: \mathbb{R}) - 1)})))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.EAM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Section V A, Eqs. (49)–(50), takes n greater than d normalized kets. Their projectors sum to n/d times the identity, and distinct kets have squared overlap (n-d)/(d(n-1)). Scaling their projectors by d/n gives measurement effects. Both the resolution of the identity and the prescribed overlap are included in the type.

**Definition 1.11 (The equiangular measurement effects).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (A: \operatorname{EAM}\left(d, n\right)), \forall (a: \operatorname{Fin}\left(n\right)), (A).effect\left(a\right) = \operatorname{smul}\left(\frac{(d: \mathbb{C})}{(n: \mathbb{C})}, \operatorname{proj}\left((A).val\left(a\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.effect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The a-th effect is d/n times the projector of the a-th ket, as in Section V A. For positive d the effects sum to the identity.

**Definition 1.12 (The EAM joint-probability table).**

$$\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (rho: \operatorname{BipartiteOp}\left(d\right)), \forall (A: \operatorname{EAM}\left(d, n\right)), \forall (B: \operatorname{EAM}\left(d, n\right)), \operatorname{Pn}\left(rho, A, B\right) = \operatorname{correlation}\left(rho, (A).effect, (B).effect\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.Pn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The two sides choose equiangular measurements independently, with the same local dimension and number of outcomes. Pn is the n by n table formed from their effects.

**Theorem 1.13 (The Hilbert–Schmidt product bound).**

$$\forall (K: Type*), [\operatorname{Fintype}\left(K\right)] \forall (R: \operatorname{Matrix}\left(K, K, \mathbb{C}\right)), \forall (S: \operatorname{Matrix}\left(K, K, \mathbb{C}\right)), \operatorname{traceNorm}\left(R \cdot S\right) \le \sqrt{\operatorname{entryNormSq}\left(R\right)} \cdot \sqrt{\operatorname{entryNormSq}\left(S\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For square complex matrices on any finite index type, the trace norm of their product is at most the product of their Frobenius norms. Here entryNormSq(M) is the sum of the squared absolute values of all entries of M. This is the Hilbert–Schmidt Hölder inequality, and it includes the empty index type.

**Theorem 1.14 (Normalization as a conjugate dot product).**

$$\forall (I: Type*), [\operatorname{Fintype}\left(I\right)] \forall (u: \operatorname{Ket}\left(I\right)), \operatorname{dotProduct}\left(\operatorname{star}\left((u).vec\right), (u).vec\right) = (1: \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.ket_dot_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The conjugate dot product of a normalized ket with itself equals one, in the complex field.

**Theorem 1.15 (The projector as an outer product).**

$$\forall (I: Type*), [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall (u: \operatorname{Ket}\left(I\right)), \operatorname{proj}\left(u\right) = \operatorname{vecMulVec}\left((u).vec, \operatorname{star}\left((u).vec\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj_eq_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The pure-state matrix equals the outer product of the ket and its complex conjugate. This identifies its entries with the coordinates used in matrix factorization.

**Theorem 1.16 (Scaled pure projectors are Hermitian).**

$$\forall (d: \mathbb{N}), \forall (A: \operatorname{Op}\left(d\right)), (\operatorname{ScaledPure}\left(A\right)) \Rightarrow (\operatorname{IsHermitian}\left(A\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.scaledPure_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

A pure projector is Hermitian, and multiplication by a real scalar preserves Hermiticity.

**Theorem 1.17 (Compression by a scaled pure projector).**

$$\forall (d: \mathbb{N}), \forall (A: \operatorname{Op}\left(d\right)), (\operatorname{ScaledPure}\left(A\right)) \Rightarrow (\forall (M: \operatorname{Op}\left(d\right)), A \cdot M \cdot A = \operatorname{smul}\left(\operatorname{trace}\left(M \cdot A\right), A\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.scaledPure_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Sandwiching an arbitrary operator M between two copies of a scaled pure projector multiplies that projector by the trace of M times the projector. The trace is complex and no Hermitian hypothesis on M is required.

**Theorem 1.18 (Trace overlap of two pure projectors).**

$$\forall (d: \mathbb{N}), \forall (u: \operatorname{Ket}\left(\operatorname{Fin}\left(d\right)\right)), \forall (v: \operatorname{Ket}\left(\operatorname{Fin}\left(d\right)\right)), \operatorname{trace}\left(\operatorname{proj}\left(u\right) \cdot \operatorname{proj}\left(v\right)\right) = ((\left\lVert \operatorname{dotProduct}\left(\operatorname{star}\left((u).vec\right), (v).vec\right) \right\rVert)^{2}: \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

The trace of the product of two pure projectors is the squared absolute overlap of their normalized kets, regarded as a complex number.

**Theorem 1.19 (From second moments to a Schmidt-number bound).**

$$\forall (d: \mathbb{N}), \forall (r: \mathbb{N}), \forall (I: Type*), [\operatorname{Fintype}\left(I\right)] \forall (rho: \operatorname{BipartiteOp}\left(d\right)), \forall (A: (I \to \operatorname{Op}\left(d\right))), \forall (B: (I \to \operatorname{Op}\left(d\right))), \forall (alpha: \mathbb{R}), \forall (beta: \mathbb{R}), (\forall (a: I), \operatorname{ScaledPure}\left(A\left(a\right)\right)) \Rightarrow ((\forall (b: I), \operatorname{ScaledPure}\left(B\left(b\right)\right)) \Rightarrow ((0 \le alpha) \Rightarrow ((0 \le beta) \Rightarrow ((\operatorname{MomentBound}\left(A, alpha, beta\right)) \Rightarrow ((\operatorname{MomentBound}\left(B, alpha, beta\right)) \Rightarrow ((\operatorname{SchmidtNumberLE}\left(rho, r\right)) \Rightarrow (\operatorname{traceNorm}\left(\operatorname{correlation}\left(rho, A, B\right)\right) \le alpha + beta \cdot (r: \mathbb{R}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Two finite families of nonnegative multiples of pure projectors with the same nonnegative second-moment coefficients alpha and beta give a correlation table of trace norm at most alpha plus beta r on every state of Schmidt number at most r. The index type and the dimensions may be empty; this general statement adds no positivity assumptions on d or r.

**Definition 1.20 (Tavakoli–Morelli Conjecture 2).**

$$(claim) \Leftrightarrow (\forall (d: \mathbb{N}), \forall (n: \mathbb{N}), \forall (r: \mathbb{N}), (1 \le d) \Rightarrow ((1 \le r) \Rightarrow ((r \le d) \Rightarrow (\forall (A: \operatorname{EAM}\left(d, n\right)), \forall (B: \operatorname{EAM}\left(d, n\right)), \forall (rho: \operatorname{BipartiteOp}\left(d\right)), (\operatorname{SchmidtNumberLE}\left(rho, r\right)) \Rightarrow (\operatorname{traceNorm}\left(\operatorname{Pn}\left(rho, A, B\right)\right) \le \frac{(d: \mathbb{R}) \cdot ((d: \mathbb{R}) - 1) + (r: \mathbb{R}) \cdot ((n: \mathbb{R}) - (d: \mathbb{R}))}{(n: \mathbb{R}) \cdot ((n: \mathbb{R}) - 1)})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.claim` (`✓ std3`).

*Citation.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

Section V A, Conjecture 2, Eq. (52), asserts the displayed bound for a state of Schmidt number r. Since the bound increases with r, the statement uses Schmidt number at most r. It includes every positive local dimension, every r from one to d, and every pair of equiangular measurements with the same n greater than d. All subtractions in the bound are real subtractions.

**Theorem 1.21 (The equiangular Schmidt-number bound).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.result` (`✓ std3`). ∎

*Resolves.* `Problems/tavakoli-morelli-2024-conjecture-2-incomplete-eam-schmidt-bound` (proved) by `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tavakoli-morelli-2024-conjecture-2-incomplete-eam-schmidt-bound","declaration_gid":"D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli; Simon Morelli (2024). *Enhanced Schmidt number criteria based on correlation trace norms*. DOI: [10.1103/PhysRevA.110.062417](https://doi.org/10.1103/PhysRevA.110.062417). URL: <https://arxiv.org/abs/2402.09972v2>.

*Commentary.*

For a pure ket, write its coefficient matrix as U D V adjoint by the singular value decomposition, with D diagonal and nonnegative. Put S equal to the positive square root of D. The correlation table factors as F adjoint times G, whose columns are the vectorizations of S U adjoint A_a U S and S V adjoint transpose(B_b) V S. The Hilbert–Schmidt Hölder inequality bounds its trace norm by the product of the two Frobenius norms. For rank-one effects, the squared Frobenius norms are the second moments of the corresponding Hermitian weight matrices.

The equiangular Gram matrix and Cauchy–Schwarz give, for every Hermitian H, the second-moment bound with coefficients alpha = d(d-1)/(n(n-1)) and beta = (n-d)/(n(n-1)). For each weight matrix the quadratic trace is the sum of squared Schmidt coefficients, equal to one, while the squared trace is (sum of Schmidt coefficients) squared, at most r by Cauchy–Schwarz on their at most r nonzero entries. Thus the pure-state bound is alpha plus beta r. Real linearity of the probability table, the trace-norm triangle inequality, and homogeneity for nonnegative weights extend the bound to convex mixtures. Substitution of alpha and beta yields claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.BipartiteOp`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.EAM`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.MomentBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.Op`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.Pn`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.ScaledPure`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.SchmidtNumberLE`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.coeff`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.correlation`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.effect`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.ket_dot_self`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj_eq_outer`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.proj_overlap`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.scaledPure_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.scaledPure_sandwich`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.schmidt_traceNorm_le_of_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.traceNorm_mul_le_hsSq`
- Dependency: [D5/S3/Observer/BornReduction](../../Observer/BornReduction.md)
- Dependency: [D5/S3/QuadraticForms/GerzonEqualityParameterIdentity](../../QuadraticForms/GerzonEqualityParameterIdentity.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/IdealNorm](../Analysis/TraceClass/IdealNorm.md)
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](PrecessionSpinOneSeparableBound.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
- Dependency: [D5/S3/Quantum/Tomography/PurityPythagorasDecomposition](../Tomography/PurityPythagorasDecomposition.md)
