# The Gurvits--Barnum separable ball

## Abstract

Block positivity bounds the Frobenius sum by the real trace and gives a separable ball about a scalar identity.

All matrices act on the product index set Fin m times Fin n. SeparableCone consists of finite sums of Kronecker products of positive semidefinite factors. BlockPositive means that the real quadratic form is nonnegative on every product vector. The Frobenius sum below is the sum of squared entry norms, independently of any default norm on matrices. Empty index sets and a ball of radius zero are included.

**Theorem 1.1 (Block-positive Frobenius bound).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (H:Fin\left(m\right)\times Fin\left(n\right)\to Fin\left(m\right)\times Fin\left(n\right)\to \mathbb{C}), ((Hermitian\left(H\right))\land (BlockPositive\left(H\right)))\Rightarrow (0\leq Re\left(tr\left(H\right)\right))\land (\sum_{u:Fin\left(m\right)\times Fin\left(n\right)} \sum_{v:Fin\left(m\right)\times Fin\left(n\right)} \left\lVert H\left(u, v\right) \right\rVert^{2}\leq (Re\left(tr\left(H\right)\right))^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.frobSq_le_trace_sq_of_blockPositive` (`✓ std3`). ∎

*Citation.* Leonid Gurvits and Howard Barnum (2002). *Largest separable balls around the maximally mixed bipartite quantum state*. DOI: [10.1103/PhysRevA.66.062311](https://doi.org/10.1103/PhysRevA.66.062311). URL: <https://doi.org/10.1103/PhysRevA.66.062311>.

*Commentary.*

Szarek--Werner--Zyczkowski, J. Math. Phys. 49, 032113 (2008), printed page 18, states Tr(H squared) ≤ (Tr H) squared for block-positive H, as quoted in the Gurvits--Barnum note. For Hermitian H, the entrywise Frobenius sum equals Tr(H squared), so the formal inequality is the same statement, with the nonnegative real trace also made explicit. Compressing H against a vector in either factor gives a positive semidefinite matrix. Its trace square bounds its Frobenius sum. Applying the corrected finite fourth-moment identity in each factor gives two inequalities whose partial-trace terms cancel. Product basis vectors give the nonnegative trace.

**Theorem 1.2 (Separable ball criterion).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (A:Fin\left(m\right)\times Fin\left(n\right)\to Fin\left(m\right)\times Fin\left(n\right)\to \mathbb{C}), \forall (c:\mathbb{R}), ((PSD\left(A\right))\land ((0\leq c)\land (\sum_{u:Fin\left(m\right)\times Fin\left(n\right)} \sum_{v:Fin\left(m\right)\times Fin\left(n\right)} \left\lVert (A-c\cdot I)\left(u, v\right) \right\rVert^{2}\leq c^{2})))\Rightarrow SeparableCone\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_of_frob_ball` (`✓ std3`). ∎

*Citation.* Leonid Gurvits and Howard Barnum (2002). *Largest separable balls around the maximally mixed bipartite quantum state*. DOI: [10.1103/PhysRevA.66.062311](https://doi.org/10.1103/PhysRevA.66.062311). URL: <https://doi.org/10.1103/PhysRevA.66.062311>.

*Commentary.*

Gurvits--Barnum Theorem 1, printed page 4, states that I + Delta is separable when Delta is Hermitian and its Frobenius norm is at most one. The formal statement is its scalar form A = c(I + Delta), using the scaling in Corollary 2, printed page 5; c = 0 gives the zero matrix. If the PSD matrix were outside the separable cone, the separation theorem would give a block-positive matrix with negative Hilbert--Schmidt pairing. Its Hermitian part preserves both product quadratic forms and pairing with the given PSD matrix. The Frobenius bound and Cauchy--Schwarz force that pairing to be nonnegative throughout the stated ball, a contradiction.

**Theorem 1.3 (Unit rank-one complement).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (psi:Fin\left(m\right)\times Fin\left(n\right)\to \mathbb{C}), (\sum_{u:Fin\left(m\right)\times Fin\left(n\right)} \left\lVert psi\left(u\right) \right\rVert^{2}=1)\Rightarrow SeparableCone\left((I-vecMulVec\left(psi, star\left(psi\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_one_sub_rankOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A unit vector gives an orthogonal rank-one projection of trace one and Frobenius sum one. Its complement is PSD and lies in the radius-one ball about the identity. This supplies the codimension-one ray in a spectral decomposition.

**Theorem 1.4 (Projection ray).**

$$\forall (m:\mathbb{N}), \forall (n:\mathbb{N}), \forall (Q:Fin\left(m\right)\times Fin\left(n\right)\to Fin\left(m\right)\times Fin\left(n\right)\to \mathbb{C}), \forall (ell:\mathbb{R}), ((Hermitian\left(Q\right))\land ((Q\cdot Q=Q)\land ((tr\left(Q\right)=ell)\land (1\leq ell))))\Rightarrow SeparableCone\left(((ell+1)\cdot I-2\cdot Q)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_scaled_one_sub_two_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian idempotent Q of real trace ell at least one, the matrix is PSD: it is the sum of ell minus one times the identity and twice the complement of Q. Its squared distance from ell plus one times the identity is 4 ell, which is at most the square of ell plus one. The real trace parameter includes integer ranks by coercion. This supplies the complementary high-rank rays in a spectral decomposition.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.frobSq_le_trace_sq_of_blockPositive`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_of_frob_ball`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_one_sub_rankOne`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_scaled_one_sub_two_projection`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumMoments](GurvitsBarnumMoments.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../../GNSMatrix.md)
- Dependency: [D5/S3/Resource/SeparableConeResidualWitness](../../../Resource/SeparableConeResidualWitness.md)
