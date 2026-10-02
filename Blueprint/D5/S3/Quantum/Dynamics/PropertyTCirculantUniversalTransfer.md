# A property-T circulant with universal perfect state transfer

## Abstract

The circulant Circ(0, a, conj(a)) with a = (-4 sqrt(3) + i)/7 is a Hermitian circulant on three vertices whose nonzero entries have modulus 1 and whose continuous-time quantum walk has perfect state transfer between every pair of vertices, yet it is switching equivalent neither to K_2 nor to Circ(0, -i, i). This refutes the conjecture of E. Connelly, N. Grammel, M. Kraut, L. Serazo and C. Tamon (arXiv:1701.04145) that these two are the only circulants with property T and universal perfect state transfer.

**Definition 1.1 (Property T).**

$$\operatorname{PropertyT}\left(A\right) \Leftrightarrow (\forall j k, (A\left(j, k\right) \ne 0) \Rightarrow \left\lVert A\left(j, k\right) \right\rVert = 1)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.PropertyT` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

A matrix A has property T when every nonzero entry of A has modulus 1. For the adjacency matrix of a graph this says that the graph is a complex unit gain graph.

**Definition 1.2 (Universal perfect state transfer).**

$$\operatorname{UPST}\left(A\right) \Leftrightarrow (\forall u v, \exists t \in \mathbb{R}, \left\lVert \operatorname{hamiltonianPropagator}\left(A, t, v, u\right) \right\rVert = 1)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.UPST` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

The continuous-time quantum walk of a Hermitian matrix A is U(t) = exp(-i t A). There is perfect state transfer from u to v at time t when the (v, u) entry of U(t) has modulus 1, and A has universal perfect state transfer when this happens, at some real time, for all vertices u and v.

**Definition 1.3 (Switching equivalence).**

$$\operatorname{SwitchingEquivalent}\left(A, B\right) \Leftrightarrow (\exists \sigma, \exists d, (\forall i, d\left(i\right) \ne 0) \land (\operatorname{perm}\left(\sigma\right) \operatorname{diag}\left(d\right) A = B \operatorname{perm}\left(\sigma\right) \operatorname{diag}\left(d\right)))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.SwitchingEquivalent` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

A monomial matrix is the product of a permutation matrix and an invertible diagonal matrix, and two matrices A and B are switching equivalent when M A = B M for some monomial matrix M. Here M is the permutation matrix of a bijection sigma between the vertex sets times the diagonal matrix of a vector d with no zero entry.

**Definition 1.4 (The complete graph on two vertices).**

$$\operatorname{K2} = \operatorname{Circ}\left(0, 1\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.K2` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

The circulant Circ(0, 1) on Z/2Z, the adjacency matrix of K_2. Here Circ(a) is the circulant matrix with entries Circ(a)_(jk) = a_(k - j), the transpose of the circulant matrix of Mathlib.

**Definition 1.5 (The oriented triangle).**

$$\operatorname{orientedTriangle} = \operatorname{Circ}\left(0, -i, i\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.orientedTriangle` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

The circulant Circ(0, -i, i) on Z/3Z, the oriented triangle, which has universal perfect state transfer.

**Definition 1.6 (The conjecture).**

$$claim \Leftrightarrow (\forall n, (n \ge 2) \Rightarrow \forall a : \operatorname{ZMod}\left(n\right) \to \mathbb{C}, (a\left(0\right) = 0) \Rightarrow \left((\operatorname{IsHermitian}\left(\operatorname{Circ}\left(a\right)\right)) \Rightarrow \left((\operatorname{PropertyT}\left(\operatorname{Circ}\left(a\right)\right)) \Rightarrow \left((\operatorname{UPST}\left(\operatorname{Circ}\left(a\right)\right)) \Rightarrow \left(\operatorname{SwitchingEquivalent}\left(\operatorname{Circ}\left(a\right), \operatorname{K2}\right) \lor \operatorname{SwitchingEquivalent}\left(\operatorname{Circ}\left(a\right), \operatorname{orientedTriangle}\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.claim` (`✓ std3`).

*Citation.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

The conjecture of the paper, read together with its introduction, which names K_2 and Circ(0, -i, i) as the only known examples and conjectures that this set is unique: every Hermitian circulant Circ(a) on Z/nZ with n at least 2, without loops (a_0 = 0), with property T and universal perfect state transfer is switching equivalent to K_2 or to Circ(0, -i, i).

**Theorem 1.7 (A counterexample on three vertices).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result` (`✓ std3`). ∎

*Resolves.* `Problems/connelly-2017-property-t-universal-state-transfer` (refuted) by `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"connelly-2017-property-t-universal-state-transfer","declaration_gid":"D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Erin Connelly, Nathaniel Grammel, Michael Kraut, Luis Serazo, Christino Tamon (2017). *Universality in perfect state transfer*. DOI: [10.1016/j.laa.2017.06.015](https://doi.org/10.1016/j.laa.2017.06.015). URL: <https://arxiv.org/abs/1701.04145v2>.

*Commentary.*

Let a = (-4 sqrt(3) + i)/7, so that |a| = 1, and let A = Circ(0, a, conj(a)) on Z/3Z. Then A is Hermitian, has no loops and has property T. The Fourier matrix V with entries omega^(km), where omega = exp(2 pi i/3), satisfies A V = V diag(mu) with eigenvalues mu = (sqrt(3)/7)(-8, 3, 5). At t_1 = 14 sqrt(3) pi/9 the numbers -i t_1 mu_m are 2 pi i/3 times 2, 0 and 1 modulo 2 pi i, so exp(-i t_1 A) = V diag(omega^2, 1, omega) V^(-1) = omega^2 P, where P is the cyclic permutation matrix with P_(jk) = 1 exactly when k = j + 1. Hence U(t_1) = omega^2 P, U(2 t_1) = U(t_1)^2 = omega^4 P^2 and U(0) = I, and every entry of these matrices on the relevant pair of vertices has modulus 1, which gives universal perfect state transfer. The vertex sets of A and K_2 have 3 and 2 elements, so there is no bijection between them. A monomial matrix M has nonzero determinant, so M A = B M gives det A = det B; but det A = a^3 + conj(a)^3 = -360 sqrt(3)/343, while det Circ(0, -i, i) = 0. So A is switching equivalent to neither.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.K2`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.PropertyT`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.SwitchingEquivalent`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.UPST`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.orientedTriangle`
- Truth anchor: `D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.result`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](ProjectionProbabilityFlow.md)
