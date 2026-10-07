# Comparability of conical-design concurrence bounds

## Abstract

Conical two-design concurrence bounds have a uniform ratio ordering.

**Definition 1.1 (The literal tensor swap).**

$$\forall (d : \mathbb{N}), \operatorname{swap}\left(d\right) = \operatorname{Matrix}.\operatorname{submatrix}\left((1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), id, \operatorname{Prod}.\operatorname{swap}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.swap` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

The flip F in Siudzinska's Section 2, Eq. (9), p. 2, sends the computational-basis pair (a,b) to (b,a). The identity matrix is reindexed in its columns by Prod.swap, so its (p,q) entry is 1 exactly when p=(q.2,q.1). Scalars are complex.

**Definition 1.2 (A finite conical two-design).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), \forall (alpha : \mathbb{R}), \forall (beta : \mathbb{R}), \forall (positive : (\forall (i : \operatorname{Fin}\left(m\right)), (E\left(i\right)).PosSemidef)), \forall (betaPos : 0 < beta), \forall (betaLeAlpha : beta \le alpha), \forall (tensorIdentity : (\sum_{i \in \operatorname{Fin}\left(m\right)} \operatorname{Matrix}.\operatorname{kronecker}\left(E\left(i\right), E\left(i\right)\right) = (alpha : \mathbb{C}) \cdot (1 : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)) + (beta : \mathbb{C}) \cdot \operatorname{swap}\left(d\right))), (\operatorname{Design}.\operatorname{mk}\left(E, alpha, beta, positive, betaPos, betaLeAlpha, tensorIdentity\right) : \operatorname{Design}\left(d, m\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.Design` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 2, Eq. (9), p. 2: "By definition, `\mathcal{P}` is a conical 2-design if" the displayed identity is `\sum_{\alpha=1}^N\sum_{k=1}^{M_\alpha}P_{\alpha,k}\otimes P_{\alpha,k}=\kappa_+I_d\otimes I_d+\kappa_-F_d`, "where `\kappa_+\geq\kappa_->0`". The constructor below lists all data and proof fields: the positive effects, real alpha and beta, positivity of beta, beta at most alpha, and the tensor identity. Measurement labels are flattened to Fin m. No POVM normalization or fixed number of outcomes is added. The complex casts of alpha and beta are explicit.

**Definition 1.3 (The measurement correlation matrix).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), \forall (i : \operatorname{Fin}\left(m\right)), \forall (j : \operatorname{Fin}\left(m\right)), \left(P_{E}\right)\left(E, rho\right)\left(i, j\right) = \operatorname{Matrix}.\operatorname{trace}\left(rho \cdot \operatorname{Matrix}.\operatorname{kronecker}\left(E.E\left(i\right), E.E\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.P_E` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 6, Eq. (59), p. 9: "The elements of `\mathcal{B}(\rho)` in the basis of `\omega_{\alpha,k}` form the correlation matrix `\mathcal{B}_{\alpha,k;\beta,\ell}=\operatorname{Tr}[\rho(P_{\alpha,k}\otimes P_{\beta,\ell})]`." P_E is this complex square matrix, with flattened labels and the same design on both tensor factors. Its input is any bipartite complex matrix; the final claim restricts it to density states. Theorem 6 refers to Eq. (60); the defining operator expression is Eq. (59).

**Definition 1.4 (The dimension factor).**

$$\forall (d : \mathbb{N}), \operatorname{c}\left(d\right) = \operatorname{Real}.\operatorname{sqrt}\left(\frac{2}{(d : \mathbb{R}) \cdot ((d : \mathbb{R}) - 1)}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.c` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 7, Theorem 6, Eq. (74), p. 10: `\eta=\frac{1}{S}\sqrt{\frac{2}{d(d-1)}},\qquad\xi=\mathcal{C}_{\max}`. The factor c isolates the square root. Both appearances of d are real casts, and the division is real division. The final comparison assumes d at least 2.

**Definition 1.5 (The concurrence lower bound).**

$$\forall (d : \mathbb{N}), \forall (m : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), \left(B_{E}\right)\left(E, rho\right) = \frac{\operatorname{c}\left(d\right) \cdot (\operatorname{traceNorm}\left(\left(P_{E}\right)\left(E, rho\right)\right) - E.alpha - E.beta)}{E.beta}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.B_E` (`✓ std3`).

*Citation.* Katarzyna Siudzińska (2025). *Measures from conical 2-designs depend only on two constants*. DOI: [10.1088/1751-8121/ae0203](https://doi.org/10.1088/1751-8121/ae0203). URL: <https://arxiv.org/abs/2506.18211>.

*Commentary.*

Section 7, Theorem 6, Eq. (73), p. 10: "The concurrence of a mixed bipartite state `\rho` is lower bounded by" `\mathcal{N}_{\min}(\rho)=\eta\Big[\|\mathcal{B}(\rho)\|_{\tr}-\xi\Big]`. Here S=beta and C_max=alpha+beta. The frozen traceNorm is the real trace of the positive square root of X.conjTranspose times X, equivalently the sum of singular values. The expression is not truncated at zero.

**Definition 1.6 (The Wang–Zhou–Chen–Fei conjecture).**

$$claim \Leftrightarrow (\forall (d : \mathbb{N}), (2 \le d) \Rightarrow \forall (m : \mathbb{N}), \forall (n : \mathbb{N}), \forall (E : \operatorname{Design}\left(d, m\right)), \forall (G : \operatorname{Design}\left(d, n\right)), (\forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), \left(B_{E}\right)\left(G, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right) \le \left(B_{E}\right)\left(E, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)) \lor (\forall (rho : \operatorname{DensityState}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right))\right)), \left(B_{E}\right)\left(E, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right) \le \left(B_{E}\right)\left(G, \operatorname{CStarMatrix}.\operatorname{ofMatrix}.symm\left(rho.1\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.claim` (`✓ std3`).

*Citation.* H.-F. Wang; W. Zhou; L. Chen; S.-M. Fei (2026). *Estimating the concurrence for quantum states via symmetric measurements*. URL: <https://arxiv.org/abs/2606.31010v2>.

*Commentary.*

Section IV, p. 8, after Theorem 2, verbatim: "The lower bounds of concurrence induced by arbitrary two distinct conical 2-designs are comparable." For each d at least 2 and each pair of finite designs, one ordering holds for every bipartite state. DensityState is the canonical positive semidefinite trace-one CStarMatrix; CStarMatrix.ofMatrix.symm takes its underlying Matrix. Equal designs are also included. The state quantifier lies inside each branch, so the choice of ordering is independent of the state.

**Theorem 1.7 (Uniform comparison by the ratio alpha over beta).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H.-F. Wang; W. Zhou; L. Chen; S.-M. Fei (2026). *Estimating the concurrence for quantum states via symmetric measurements*. URL: <https://arxiv.org/abs/2606.31010v2>.

*Commentary.*

Vectorize each effect as A_ip=(E_i)_(p.2,p.1). The tensor identity gives A.conjTranspose times A=beta I+alpha vv.conjTranspose, where v=Matrix.vec I. With Q=vv.conjTranspose/d and t=sqrt(1+d alpha/beta), a rectangular isometry factors A as sqrt(beta) U (I+(t-1)Q). The trace norm is unchanged by that isometry, so the bound depends only on t. For s at most t, the projection dilation gives a trace-norm gain of at least (t squared minus s squared)/d, cancelling the change of the offset. Consequently alpha_E/beta_E at least alpha_G/beta_G gives B_E at least B_G for every state. Equal ratios give equal bounds. The total order on real ratios proves claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.B_E`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.Design`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.P_E`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.c`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability.swap`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
