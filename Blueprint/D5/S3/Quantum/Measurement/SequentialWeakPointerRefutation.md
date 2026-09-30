# Three weak measurements of projections below minus one eighth

## Abstract

For three sequential weak measurements of projection observables on a pure state, without post-selection, the mean product of the pointer positions can be -1/6, below -1/8. This refutes the conjecture of A. A. Abbott, R. Silva, J. Wechs, N. Brunner and C. Branciard (arXiv:1805.09364) that -1/8 bounds this mean for every number of projection observables.

**Definition 1.1 (Nested anticommutator).**

$$\operatorname{nestedAnti}\left(0, A\right) = A\left(0\right),\qquad\operatorname{nestedAnti}\left(n + 1, A\right) = A\left(0\right) \cdot \operatorname{nestedAnti}\left(n, A \circ \operatorname{succ}\right) + \operatorname{nestedAnti}\left(n, A \circ \operatorname{succ}\right) \cdot A\left(0\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.nestedAnti` (`✓ std3`).

*Citation.* Alastair A. Abbott; Ralph Silva; Julian Wechs; Nicolas Brunner; Cyril Branciard (2019). *Anomalous Weak Values Without Post-Selection*. DOI: [10.22331/q-2019-10-14-194](https://doi.org/10.22331/q-2019-10-14-194). URL: <https://arxiv.org/abs/1805.09364v3>.

*Commentary.*

The nested anticommutator of n + 1 matrices A_0, ..., A_n is A_0 for n = 0 and {A_0, {A_1, ..., {A_(n-1), A_n}...}} in general, defined by recursion on n; A o succ denotes the family A_1, ..., A_n.

**Definition 1.2 (Mean product of the pointer positions).**

$$\operatorname{pointerMean}\left(A, \psi\right) = 2^{-n} \cdot \operatorname{Re} \langle\psi, \operatorname{nestedAnti}\left(n, A\right) \psi\rangle$$

*Formalization.* `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.pointerMean` (`✓ std3`).

*Citation.* Alastair A. Abbott; Ralph Silva; Julian Wechs; Nicolas Brunner; Cyril Branciard (2019). *Anomalous Weak Values Without Post-Selection*. DOI: [10.22331/q-2019-10-14-194](https://doi.org/10.22331/q-2019-10-14-194). URL: <https://arxiv.org/abs/1805.09364v3>.

*Commentary.*

In the weak regime without post-selection, the mean product of the pointer positions of n + 1 sequential measurements of A_0, ..., A_n on the pure state psi is 2^(-n) times the real part of <psi, N psi>, where N is the nested anticommutator and <psi, phi> is the sum over i of the conjugate of psi_i times phi_i.

**Definition 1.3 (The conjectured bound minus one eighth).**

$$claim \Leftrightarrow (\forall d : \mathbb{N}, \forall n : \mathbb{N}, \forall A : \operatorname{Fin}\left(n + 1\right) \to \mathbb{C}^{d\times d}, (\forall i : \operatorname{Fin}\left(n + 1\right), \operatorname{IsStarProjection}\left(A\left(i\right)\right)) \Rightarrow \forall \psi : \mathbb{C}^{d}, (\langle\psi, \psi\rangle = 1) \Rightarrow -\frac{1}{8} \le \operatorname{pointerMean}\left(A, \psi\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.claim` (`✓ std3`).

*Citation.* Alastair A. Abbott; Ralph Silva; Julian Wechs; Nicolas Brunner; Cyril Branciard (2019). *Anomalous Weak Values Without Post-Selection*. DOI: [10.22331/q-2019-10-14-194](https://doi.org/10.22331/q-2019-10-14-194). URL: <https://arxiv.org/abs/1805.09364v3>.

*Commentary.*

The conjecture: for every dimension d, every number n + 1 of observables, every family of orthogonal projections A_i on C^d (A_i^2 = A_i and A_i^* = A_i, the projection observables with eigenvalues 0 and 1) and every unit vector psi, the mean product of the pointer positions is at least -1/8. The paper proves this bound for two observables.

**Theorem 1.4 (A sequence of three projections below minus one eighth).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/abbott-2019-sequential-weak-pointer-bound` (refuted) by `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abbott-2019-sequential-weak-pointer-bound","declaration_gid":"D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Alastair A. Abbott; Ralph Silva; Julian Wechs; Nicolas Brunner; Cyril Branciard (2019). *Anomalous Weak Values Without Post-Selection*. DOI: [10.22331/q-2019-10-14-194](https://doi.org/10.22331/q-2019-10-14-194). URL: <https://arxiv.org/abs/1805.09364v3>.

*Commentary.*

Take d = 3, the state e_3, and the rational projections P_1 = (1/3)[[1, 1, -1], [1, 1, -1], [-1, -1, 1]] onto (1, 1, -1), P_2 = [[1, 0, 0], [0, 1/2, 1/2], [0, 1/2, 1/2]] = I - v v^* with v = (0, 1, -1)/sqrt(2), and P_3 = [[1/2, 0, 1/2], [0, 1, 0], [1/2, 0, 1/2]] = I - w w^* with w = (1, 0, -1)/sqrt(2). Each satisfies P^2 = P = P^*, checked entrywise, and e_3 is a unit vector. Evaluating the nested anticommutator gives (1/4) <e_3, {P_1, {P_2, P_3}} e_3> = -1/6 < -1/8, so the conjectured bound fails for three observables.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.nestedAnti`
- Truth anchor: `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.pointerMean`
- Truth anchor: `D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result`
