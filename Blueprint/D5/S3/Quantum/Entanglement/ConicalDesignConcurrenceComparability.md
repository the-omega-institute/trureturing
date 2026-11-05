# Comparability of conical-design concurrence bounds

## Abstract

Conical two-design concurrence bounds have a uniform ratio ordering.

**Theorem 1.1 (Nonnegative homogeneity of the trace norm).**

$$\forall (n : Type*), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall (X : \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \forall (c : \mathbb{R}), (0 \le c) \Rightarrow \operatorname{traceNorm}\left(\operatorname{smul}\left((c : \mathbb{C}), X\right)\right) = c \cdot \operatorname{traceNorm}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of a complex matrix by a nonnegative real scalar multiplies its trace norm by the same scalar. This includes zero and allows convex trace-norm estimates to pass from pure states to mixtures.

**Theorem 1.2 (Rectangular isometries preserve the trace norm).**

$$\forall (M : Type*), \forall (N : Type*), [\operatorname{Fintype}\left(M\right)] [\operatorname{DecidableEq}\left(M\right)] [\operatorname{Fintype}\left(N\right)] [\operatorname{DecidableEq}\left(N\right)], \forall (V : \operatorname{Matrix}\left(M, N, \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{conjTranspose}\left(V\right) \cdot V = (1 : \operatorname{Matrix}\left(N, N, \mathbb{C}\right))) \Rightarrow \forall (X : \operatorname{Matrix}\left(N, N, \mathbb{C}\right)), \operatorname{traceNorm}\left(V \cdot X \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(V\right)\right) = \operatorname{traceNorm}\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.traceNorm_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite index types M and N, a complex rectangular matrix V with adjoint times V equal to the identity preserves the trace norm under X mapped to V X V adjoint. The square matrix X is arbitrary. This invariance is used in the normal form of the concurrence bound and in the projection dilation.

**Definition 1.3 (The literal tensor swap).**

$$\forall (d : \mathbb{N}), \operatorname{swap}\left(d\right) = \operatorname{Matrix}.\operatorname{submatrix}\left((1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), id, \operatorname{Prod}.\operatorname{swap}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.swap` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

The flip F in Siudzinska's Section 2, Eq. (9), p. 2, sends the computational-basis pair (a,b) to (b,a). The identity matrix is reindexed in its columns by Prod.swap, so its (p,q) entry is 1 exactly when p=(q.2,q.1). Scalars are complex.

**Definition 1.4 (A finite conical two-design).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), \forall (alpha : \mathbb{R}), \forall (beta : \mathbb{R}), \forall (positive : (\forall (i : \operatorname{Fin}\left(m\right)), (E\left(i\right)).PosSemidef)), \forall (betaPos : 0 < beta), \forall (betaLeAlpha : beta \le alpha), \forall (tensorIdentity : (\sum_{i \in \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{kronecker}\left(E\left(i\right), E\left(i\right)\right) = (alpha : \mathbb{C}) \cdot (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)) + (beta : \mathbb{C}) \cdot \operatorname{swap}\left(d\right))), (\operatorname{Design}.\operatorname{mk}\left(E, alpha, beta, positive, betaPos, betaLeAlpha, tensorIdentity\right) : \operatorname{Design}\left(d, m\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.Design` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 2, Eq. (9), p. 2: "By definition, `\mathcal{P}` is a conical 2-design if" the displayed identity is `\sum_{\alpha=1}^N\sum_{k=1}^{M_\alpha}P_{\alpha,k}\otimes P_{\alpha,k}=\kappa_+I_d\otimes I_d+\kappa_-F_d`, "where `\kappa_+\geq\kappa_->0`". The constructor below lists all data and proof fields: the positive effects, real alpha and beta, positivity of beta, beta at most alpha, and the tensor identity. Measurement labels are flattened to Fin m. No POVM normalization or fixed number of outcomes is added. The complex casts of alpha and beta are explicit.

**Definition 1.5 (The measurement correlation matrix).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(m\right)), \forall (j : \operatorname{Fin}\left(m\right)), \left(P_{E}\right)\left(E, rho\right)\left(i, j\right) = \operatorname{Matrix}.\operatorname{trace}\left(rho \cdot \operatorname{Matrix}.\operatorname{kronecker}\left(E.E\left(i\right), E.E\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.P_E` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 6, Eq. (59), p. 9: "The elements of `\mathcal{B}(\rho)` in the basis of `\omega_{\alpha,k}` form the correlation matrix `\mathcal{B}_{\alpha,k;\beta,\ell}=\operatorname{Tr}[\rho(P_{\alpha,k}\otimes P_{\beta,\ell})]`." P_E is this complex square matrix, with flattened labels and the same design on both tensor factors. Its input is any bipartite complex matrix; the final claim restricts it to density states. Theorem 6 refers to Eq. (60); the defining operator expression is Eq. (59).

**Definition 1.6 (The dimension factor).**

$$\forall (d : \mathbb{N}), \operatorname{c}\left(d\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{2}{(d : \mathbb{R}) \cdot ((d : \mathbb{R}) - 1)}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.c` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 7, Theorem 6, Eq. (74), p. 10: `\eta=\frac{1}{S}\sqrt{\frac{2}{d(d-1)}},\qquad\xi=\mathcal{C}_{\max}`. The factor c isolates the square root. Both appearances of d are real casts, and the division is real division. The final comparison assumes d at least 2.

**Definition 1.7 (The concurrence lower bound).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), \left(B_{E}\right)\left(E, rho\right) = \frac{\operatorname{c}\left(d\right) \cdot (\operatorname{traceNorm}\left(\left(P_{E}\right)\left(E, rho\right)\right) - E.alpha - E.beta)}{E.beta}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.B_E` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 7, Theorem 6, Eq. (73), p. 10: "The concurrence of a mixed bipartite state `\rho` is lower bounded by" `\mathcal{N}_{\min}(\rho)=\eta\Big[\|\mathcal{B}(\rho)\|_{\tr}-\xi\Big]`. Here S=beta and C_max=alpha+beta. The frozen traceNorm is the real trace of the positive square root of X.conjTranspose times X, equivalently the sum of singular values. The expression is not truncated at zero.

**Definition 1.8 (The Wang–Zhou–Chen–Fei conjecture).**

$$claim \Leftrightarrow (\forall (d : \mathbb{N}), (2 \le d) \Rightarrow \forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (G : \operatorname{Design}\left(d, n\right)), (\forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), \left(B_{E}\right)\left(G, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right) \le \left(B_{E}\right)\left(E, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)) \lor (\forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), \left(B_{E}\right)\left(E, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right) \le \left(B_{E}\right)\left(G, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.claim` (`✓ std3`).

*Citation.* H.-F. Wang; W. Zhou; L. Chen; S.-M. Fei (2026). *Estimating the concurrence for quantum states via symmetric measurements*. URL: <https://arxiv.org/abs/2606.31010v2>.

*Commentary.*

Section IV, p. 8, after Theorem 2, verbatim: "The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable." For each d at least 2 and each pair of finite designs, one ordering holds for every bipartite state. DensityState is the canonical positive semidefinite trace-one CStarMatrix; CStarMatrix.ofMatrix.symm takes its underlying Matrix. Equal designs are also included. The state quantifier lies inside each branch, so the choice of ordering is independent of the state.

**Theorem 1.9 (Uniform comparison by the ratio alpha over beta).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-zhou-chen-fei-2026-conical-design-concurrence-comparability` (proved) by `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-zhou-chen-fei-2026-conical-design-concurrence-comparability","declaration_gid":"D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H.-F. Wang; W. Zhou; L. Chen; S.-M. Fei (2026). *Estimating the concurrence for quantum states via symmetric measurements*. URL: <https://arxiv.org/abs/2606.31010v2>.

*Commentary.*

Vectorize each effect as A_ip=(E_i)_(p.2,p.1). The tensor identity gives A.conjTranspose times A=beta I+alpha vv.conjTranspose, where v=Matrix.vec I. With Q=vv.conjTranspose/d and t=sqrt(1+d alpha/beta), a rectangular isometry factors A as sqrt(beta) U (I+(t-1)Q). The trace norm is unchanged by that isometry, so the bound depends only on t. For s at most t, the projection dilation gives a trace-norm gain of at least (t squared minus s squared)/d, cancelling the change of the offset. Consequently alpha_E/beta_E at least alpha_G/beta_G gives B_E at least B_G for every state. Equal ratios give equal bounds. The total order on real ratios proves claim.

## A physical six-effect family with a strict comparison

This analytical application uses the existing bound_normal_form and ratio ordering in this module. The physical realization and singular-value calculation below are mathematical exposition, not additional kernel-checked declarations. The cited Wang–Zhou–Chen–Fei and Siudzinska sources supply the conjecture and bound conventions; no priority claim for this example is made.

### Six complex effects and their design constants

Work on the complex two-qubit space, in computational order 00, 01, 10, 11. For every real parameter in the following interval, take both signs for each of the three ordinary Pauli matrices (i denotes the complex imaginary unit):

$$
0<\lambda\leq\frac{1}{\sqrt{2}}
$$

$$
\sigma_{x}=\begin{bmatrix}0&1\\1&0\end{bmatrix},\quad \sigma_{y}=\begin{bmatrix}0&-i\\i&0\end{bmatrix},\quad \sigma_{z}=\begin{bmatrix}1&0\\0&-1\end{bmatrix}
$$

$$
\left(E_{k,\pm}\right)\left(\lambda\right)=\frac{I_{2}}{2}\pm\frac{\lambda}{\sqrt{2}}\sigma_{k},\quad k\in\{x,y,z\}
$$

Each Pauli matrix is Hermitian with eigenvalues +1 and -1, so every effect has eigenvalues $\frac{1}{2}\pm\frac{\lambda}{\sqrt{2}}$. They lie between zero and one on the whole interval. Every effect has trace one and is nonzero. At the included upper endpoint its eigenvalues are zero and one, so it is rank one; positive definiteness is not required. Each plus/minus pair sums to the identity. The six effects sum to three times the identity: they are three binary POVMs, not one globally normalized six-outcome POVM, and no rescaling is applied.

Suppress the common argument lambda in the effects below. The cross terms cancel within each pair, giving

$$
\sum_{s=\pm}\operatorname{kronecker}\left(E_{k,s}, E_{k,s}\right)=\frac{I_{4}}{2}+\lambda^{2}\operatorname{kronecker}\left(\sigma_{k}, \sigma_{k}\right)
$$

Here kronecker denotes the tensor product. For the literal tensor swap F, entrywise evaluation of the displayed Pauli matrices gives the first identity below, and summing the three pair identities gives the second:

$$
\sum_{k}\operatorname{kronecker}\left(\sigma_{k}, \sigma_{k}\right)=2F-I_{4}
$$

$$
\sum_{k,s}\operatorname{kronecker}\left(E_{k,s}, E_{k,s}\right)=(\frac{3}{2} - \lambda^{2})I_{4}+2\lambda^{2}F
$$

$$
\alpha=\frac{3}{2} - \lambda^{2},\quad \beta=2\lambda^{2},\quad \alpha-\beta=3(\frac{1}{2} - \lambda^{2})\geq0
$$

Thus alpha is at least beta and beta is strictly positive, exactly as required by Design. The value lambda = 0 is excluded: it would give beta = 0 and leave the bound undefined.

### A mixed density state and the same-design convention

$$
\phi_{2}=\frac{|00\rangle + |11\rangle}{\sqrt{2}},\quad \rho_{*}=\frac{1}{2}|\phi_{2}\rangle\langle\phi_{2}|+\frac{1}{2}|01\rangle\langle01|
$$

Both displayed vectors have norm one and are orthogonal. Each projector is positive semidefinite with trace one; their equal mixture is therefore positive semidefinite with trace one and has rank two. It is an actual mixed density state. Use the six effects in the order x+, x-, y+, y-, z+, z- on both subsystems. In particular, the second effect is not complex-conjugated, which matters for the imaginary entries of the y Pauli matrix:

$$
\left(P_{E}\right)\left(\rho_{*}\right)_{i,j}=\operatorname{tr}\left(\rho_{*} \cdot \operatorname{kronecker}\left(E_{i}, E_{j}\right)\right)
$$

The trace norm is the sum of singular values. For this dimension c(2) = 1, and the untruncated bound is

$$
\left(B_{E}\right)\left(\operatorname{E}\left(\lambda\right), \rho_{*}\right) = \frac{\left\lVert \left(P_{E}\right)\left(\rho_{*}\right) \right\rVert_{1} - \alpha - \beta}{\beta}
$$

Apply the owner's realignedFlip convention, $X_{(a,b),(c,e)}=\left(\rho_{*}\right)_{(a,e),(b,c)}$. In computational order this gives

$$
\rho_{*}=\begin{bmatrix}\frac{1}{4}&0&0&\frac{1}{4}\\0&\frac{1}{2}&0&0\\0&0&0&0\\\frac{1}{4}&0&0&\frac{1}{4}\end{bmatrix},\quad X=\begin{bmatrix}\frac{1}{4}&0&0&\frac{1}{2}\\0&0&\frac{1}{4}&0\\0&\frac{1}{4}&0&0\\0&0&0&\frac{1}{4}\end{bmatrix}
$$

### The entire parameter interval in the normal form

The owner's Q(2) is the projector onto the maximally entangled vector above. Set

$$
Q=|\phi_{2}\rangle\langle\phi_{2}|,\quad M_{t}=I_{4}+(t - 1)Q,\quad t=\sqrt{1 + \frac{2 \cdot \alpha}{\beta}}=\sqrt{\frac{3}{2 \cdot \lambda^{2}}}\geq\sqrt{3}
$$

Use the orthonormal basis consisting, in order, of $\phi_{2}$, $\frac{|00\rangle - |11\rangle}{\sqrt{2}}$, |01>, and |10>. The last two coordinates do not couple to the first two, and M_t acts as diag(t,1,1,1). Consequently the transformed matrix has the following two diagonal blocks:

$$
M_{t}XM_{t}=\begin{bmatrix}\frac{t^{2}}{2}&-\frac{t}{4}&0&0\\\frac{t}{4}&0&0&0\\0&0&0&\frac{1}{4}\\0&0&\frac{1}{4}&0\end{bmatrix}
$$

$$
A=\begin{bmatrix}\frac{t^{2}}{2}&-\frac{t}{4}\\\frac{t}{4}&0\end{bmatrix},\quad H=\begin{bmatrix}0&\frac{1}{4}\\\frac{1}{4}&0\end{bmatrix}
$$

The off-diagonal signs in A are opposite. This block is not Hermitian, so its eigenvalues cannot be substituted for singular values. For the two singular values s1 and s2 of any complex 2-by-2 matrix A, the sum of their squares is tr(A* A) and their product is |det A|. Hence

$$
(s_{1} + s_{2})^{2}=\operatorname{tr}\left(A^{*} \cdot A\right)+2\left|\operatorname{det}\left(A\right)\right|
$$

$$
\operatorname{tr}\left(A^{*} \cdot A\right)=\frac{t^{4}}{4}+\frac{t^{2}}{8},\quad \operatorname{det}\left(A\right)=\frac{t^{2}}{16}
$$

Since t is positive, taking the nonnegative square root yields the first block's trace norm. The second block has two singular values equal to one quarter. Unitary invariance for the basis change and additivity over the two blocks give

$$
\left\lVert A \right\rVert_{1}=\frac{t \cdot \sqrt{t^{2} + 1}}{2},\quad \left\lVert H \right\rVert_{1}=\frac{1}{2}
$$

$$
\left\lVert M_{t} \cdot X \cdot M_{t} \right\rVert_{1}=\frac{t \cdot \sqrt{t^{2} + 1} + 1}{2}
$$

The existing bound_normal_form subtracts (t squared minus one)/2 and then one. Equivalently its offset is (t squared plus one)/2. Therefore the exact formulas throughout the stated interval are

$$
\left\lVert \left(P_{E}\right)\left(\rho_{*}\right) \right\rVert_{1}=\beta\frac{t \cdot \sqrt{t^{2} + 1} + 1}{2}
$$

$$
\left(B_{E}\right)\left(\operatorname{E}\left(\lambda\right), \rho_{*}\right)=\left\lVert M_{t} \cdot X \cdot M_{t} \right\rVert_{1}-\frac{t^{2} + 1}{2}=\frac{t \cdot \sqrt{t^{2} + 1} - t^{2}}{2}
$$

### Positive bounds with an exact strict comparison

For every allowed parameter, t is positive and sqrt(t squared plus one) is strictly larger than t. The displayed bound is thus strictly positive on the entire interval. At the included upper endpoint and at a second interior parameter it becomes

$$
\lambda=\frac{1}{\sqrt{2}}:\quad \alpha=\beta=1,\quad \frac{\alpha}{\beta}=1,\quad t=\sqrt{3},\quad \left(B_{E}\right)\left(\operatorname{E}\left(\lambda\right), \rho_{*}\right)=\sqrt{3} - \frac{3}{2}>0
$$

$$
\lambda=\frac{1}{\sqrt{6}}:\quad \alpha=\frac{4}{3},\quad \beta=\frac{1}{3},\quad \frac{\alpha}{\beta}=4,\quad t=3,\quad \left(B_{E}\right)\left(\operatorname{E}\left(\lambda\right), \rho_{*}\right)=\frac{3 \cdot \sqrt{10} - 9}{2}
$$

The strict comparison reduces to 3 sqrt(10) > 6 + 2 sqrt(3). Both sides are positive, so squaring preserves and reflects the inequality: it becomes 42 > 24 sqrt(3), or 7 > 4 sqrt(3). Squaring these positive quantities gives 49 > 48. Thus

$$
\frac{3 \cdot \sqrt{10} - 9}{2}>\sqrt{3} - \frac{3}{2}>0
$$

Because both bounds are positive, replacing each B by max(0,B) preserves this strict improvement for the same mixed state. This example does not settle strictness for every distinct ratio pair or identify concurrence for arbitrary states. The arbitrary pure-state formula and mixed-state convex-roof obligations are separate from this application.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.B_E`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.Design`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.P_E`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.c`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.swap`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.traceNorm_isometry`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
