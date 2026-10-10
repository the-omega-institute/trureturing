# Finite product-vector averages

## Abstract

Finite complex moments produce separable averages containing an arbitrary rank-one matrix.

For a vector eta on Fin m times Fin n, its reduced matrix rho_eta is the sum of the rank-one matrices of its rows. Write R_x = xx*. The finite list Omega = (0,0,0,0,sqrt(2),-sqrt(2),i sqrt(2),-i sqrt(2)) retains its four zero entries. Uniform averaging over functions g from Fin m to Fin 8 gives zero first and third moments, covariance equal to the identity, zero unconjugated second moments, and the two-pair fourth-moment identity.

**Definition 1.1 (The reduced matrix).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (eta:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}), rho\left(eta\right)=\sum_{i\in Fin\left(m\right)} R\left(row\left(eta, i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each row is a vector on Fin n. This is the matrix used in both product-vector averages.

**Lemma 1.2 (A positive product belongs to the separable cone).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (A:Matrix\left(Fin\left(m\right), Fin\left(m\right), \mathbb{C}\right)), \forall (B:Matrix\left(Fin\left(n\right), Fin\left(n\right), \mathbb{C}\right)), (PosSemidef\left(A\right))\land (PosSemidef\left(B\right))\Rightarrow separableCone\left(kronecker\left(A, B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cone includes every Kronecker product of two positive semidefinite factors. Finite sums and nonnegative real scalings preserve it.

**Theorem 1.3 (The row-contraction average).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (eta:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}), separableCone\left(R\left(eta\right)+kronecker\left(I, rho\left(eta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_rankOne_add_reduced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put y_eta(g) = sum_i conjugate(g_i) row_i(eta). The fourth moments give E R_(g tensor y_eta(g)) = R_eta + I tensor rho_eta. Every vector in this finite average is a product vector, so the matrix belongs to the separable cone.

**Theorem 1.4 (An average with a selected product component).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (chi:(Fin\left(m\right)\times Fin\left(n\right))\to \mathbb{C}), \forall (u:Fin\left(m\right)\to \mathbb{C}), \forall (v:Fin\left(n\right)\to \mathbb{C}), \forall (a:\mathbb{R}), \forall (P:Matrix\left(Fin\left(m\right), Fin\left(m\right), \mathbb{C}\right)), (IsHermitian\left(P\right))\land ((P^{2}=P)\land (\forall (j:Fin\left(n\right)), mulVec\left(P, column\left(chi, j\right)\right)=column\left(chi, j\right)))\Rightarrow separableCone\left(R\left(a\cdot product\left(u, v\right)+chi\right)+kronecker\left(P+2\cdot a^{2}\cdot R\left(u\right), rho\left(chi\right)\right)+\frac{1}{2}\cdot kronecker\left(P, R\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_projected_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a Hermitian idempotent fixing every column of chi. For real a and arbitrary local vectors u,v, set psi = a u tensor v + chi. With z(g) = (sqrt(2) a u + Pg) tensor (v/sqrt(2) + y_chi(g)), the finite average E R_z equals R_psi + (P + 2 a squared R_u) tensor rho_chi + one half P tensor R_v. The first and third moments remove the odd terms. The covariance supplies the quadratic terms, and the two fourth-moment pairings supply the rank-one and reduced-matrix terms.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.reduced`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_kronecker`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_projected_rankOne`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages.separable_rankOne_add_reduced`
