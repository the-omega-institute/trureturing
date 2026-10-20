# Tang–Zhang's sharp order −2 inequality

## Abstract

Tang–Zhang Conjecture 6.3 holds for every finite nonempty family of nonzero complex roots, with equality exactly for collinearity through the origin.

Q. Tang, T. Zhang, "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem", arXiv:2508.10341v3 (5 Dec 2025), §6, p. 31.

The identity (5.2) leads us to the following conjectural refinements of Theorem 6.1 in the case of order −2.

Conjecture 6.3. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n denote the zeros of P′(z). Then Σ_{k=1}^n 1/|w_k|² ≤ 3 Σ_{j=1}^n 1/|z_j|² + |Σ_{j=1}^n 1/z_j|². (6.9) Moreover, equality in (6.9) holds whenever z_1, …, z_n all lie on the same line passing through the origin.

In the case n = 2 we can verify Conjecture 6.3 by an explicit computation.

The last sentence is Proposition 6.4. Theorem 6.1 in the same source has the weaker right side (n+3) times the sum of reciprocal squared root moduli.

**Definition 1.1 (The polynomial with a simple root at zero).**

$$P(z)=z\prod_{j=1}^{n} (z-z_{j})$$

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.P` (`✓ std3`).

*Citation.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

The polynomial is defined for every natural n and every complex family z. For the conjecture n is at least one and each z_j is nonzero. Repeated nonzero roots are allowed.

**Definition 1.2 (The inequality and exact equality criterion).**

$$\sum_{k=1}^{n} \frac{1}{\left|w_{k}\right|^{2}}\leq 3\sum_{j=1}^{n} \frac{1}{\left|z_{j}\right|^{2}}+\left|\sum_{j=1}^{n} \frac{1}{z_{j}}\right|^{2}, (\sum_{k=1}^{n} \frac{1}{\left|w_{k}\right|^{2}}=3\sum_{j=1}^{n} \frac{1}{\left|z_{j}\right|^{2}}+\left|\sum_{j=1}^{n} \frac{1}{z_{j}}\right|^{2}) \iff \forall j, \exists r_{j}\in \mathbb{R}, z_{j}=r_{j}z_{1}$$

*Formalization.* `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

For every n at least one and every family of nonzero complex z_j, the w_k are all roots of the derivative of P, counted with multiplicity. The displayed inequality holds, and equality is equivalent to every z_j being a real multiple of the first root z_1. Thus the source's sufficient equality condition is also necessary.

**Theorem 1.3 (The sharp inequality with both equality directions).**

$$\sum_{k=1}^{n} \frac{1}{\left|w_{k}\right|^{2}}\leq 3\sum_{j=1}^{n} \frac{1}{\left|z_{j}\right|^{2}}+\left|\sum_{j=1}^{n} \frac{1}{z_{j}}\right|^{2}, (\sum_{k=1}^{n} \frac{1}{\left|w_{k}\right|^{2}}=3\sum_{j=1}^{n} \frac{1}{\left|z_{j}\right|^{2}}+\left|\sum_{j=1}^{n} \frac{1}{z_{j}}\right|^{2}) \iff \forall j, \exists r_{j}\in \mathbb{R}, z_{j}=r_{j}z_{1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result` (`✓ std3`). ∎

*Resolves.* `Problems/tang-zhang-2025-order-minus-two-schoenberg` (proved) by `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tang-zhang-2025-order-minus-two-schoenberg","declaration_gid":"D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Q. Tang, T. Zhang (2025). *Sharp Schoenberg type inequalities and the de Bruin–Sharma problem*. DOI: [10.48550/arXiv.2508.10341](https://doi.org/10.48550/arXiv.2508.10341). URL: <https://arxiv.org/abs/2508.10341v3>.

*Commentary.*

Set b_j=1/z_j, D=diag(b_j), and let J be the all-ones matrix. The inverse critical points, with multiplicity, are precisely the characteristic roots of D(I+J), a rank-one perturbation of D.

For the invertible Hermitian square root R of I+J, the similar matrix RDR has squared Frobenius norm exactly equal to the displayed right side. Schur's inequality gives the bound. Its equality criterion becomes conjugate(b_i)b_j=b_i conjugate(b_j), equivalently collinearity of the nonzero z_j through the origin.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.P`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.claim`
- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result`
- Dependency: [D5/S3/Quantum/GNSMatrix](../../Quantum/GNSMatrix.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality](SchurFrobeniusInequality.md)
