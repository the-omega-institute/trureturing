# Fourier replica products and the residual-determinant limit

## Abstract

For the fully symmetric pure Gaussian state with positive party sizes, the discrete Fourier basis of the replica torus and of the replica cycle diagonalizes the four replica Gram determinants. The resulting spectral products give the genuine multi-entropy exactly and identify the constant term of its large-squeezing expansion as a ratio of residual determinants.

**Theorem 1.1 (The tripartite replica determinant).**

$$\operatorname{det}(\alpha I-\beta Q^{T}Q)=\prod_{p,q}(\alpha-\beta\lambda_{pq})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.tripartite_gram_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be positive and let A, B, C be natural numbers with positive sum N. On the replica torus with n^2 points, let Q be the average of the three party twists with weights A/N, B/N and C/N, where A and B shift one torus coordinate each and C acts trivially. For all real alpha and beta, the determinant of alpha I - beta Q^T Q is the product over the n^2 frequency pairs (p, q) of alpha - beta lambda_pq, with lambda_pq = |A omega^p + B omega^q + C|^2 / N^2 and omega = exp(2 pi i / n). The torus characters are common eigenvectors of the twists, Q acts on them by the averaged inverse eigenvalue and Q^T by the averaged eigenvalue, and the dual Fourier matrix inverts the Fourier matrix up to the factor n^2.

**Theorem 1.2 (The bipartite replica determinant).**

$$\operatorname{det}(\alpha I-\beta Q^{T}Q)=\prod_{k}(\alpha-\beta\lambda_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.cycle_gram_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be positive and let U, V be natural numbers with positive sum. On the replica cycle of length n, let Q average the cyclic shift with weight U/(U+V) and the identity with weight V/(U+V). For all real alpha and beta, the determinant of alpha I - beta Q^T Q is the product over k in Fin n of alpha - beta lambda_k, with lambda_k = |U omega^k + V|^2 / (U+V)^2. The cycle characters diagonalize the twists and the same Fourier argument applies.

**Theorem 1.3 (Eigenvalue defects as sine weights).**

$$1-\lambda_{pq}=\frac{4w_{pq}}{N^2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.one_sub_tripartiteEigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real A, B, C with nonzero sum N and natural p, q, the defect 1 - lambda_pq equals 4 w_pq / N^2, where w_pq = AB sin^2(pi (p - q)/n) + AC sin^2(pi p/n) + BC sin^2(pi q/n). The proof writes omega^p and omega^q through cosine and sine of twice the half angles and expands the squared modulus.

**Theorem 1.4 (The Fourier product formula).**

$$GM_n=\frac{2\log P_{3}-n(\log P_{A}+\log P_{B}+\log P_{C})}{4n(n-1)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.GM3_eq_fourierGM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every replica order n >= 2, all positive integer party sizes A, B, C and every real a >= 1, put N = A + B + C and x = (a^2 - 1)/(N - 1). The genuine multi-entropy of the replica integral definition equals the displayed expression, with P_3 the product over the n^2 torus modes of 1 + x w_pq and P_i the product over k in Fin n of 1 + x u_i sin^2(pi k/n), where u_A = A(B + C), u_B = B(A + C) and u_C = C(A + B). The parameter epsilon of the symmetric state satisfies (1 - epsilon)^2 = epsilon N^2 x, so each replica factor ((1 + epsilon)/2)^2 - ((1 - epsilon)/2)^2 lambda equals epsilon (1 + x w); the powers of epsilon cancel against the one-replica normalizations.

**Definition 1.5 (The residual-determinant constant).**

$$K_{n}=\frac{2\log H_{3}-n(\log H_{A}+\log H_{B}+\log H_{C})}{4n(n-1)}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.residualConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The tripartite residual product D_3 is the product of 1 - lambda_pq over the n^2 - 1 nonconstant torus modes, and each cut residual product D_i is the product of 1 - lambda_k over the n - 1 nonconstant cycle modes. The leading coefficients are H_3 = D_3 [N^2/(4(N - 1))]^(n^2 - 1) and H_i = D_i [N^2/(4(N - 1))]^(n - 1), and K_n is the displayed combination of their logarithms.

**Theorem 1.6 (The residual-determinant limit).**

$$\lim_{a\to\infty}(GM_n+\frac{n-2}{2n}\log a)=K_{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.residual_determinant_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every replica order n >= 2 and all positive integer party sizes, the genuine multi-entropy plus ((n - 2)/(2n)) log a tends to the residual-determinant constant K_n as a tends to positive infinity. Every nonconstant Fourier mode has a positive sine weight, so each factor log(1 + x w) - 2 log a tends to log(w/(N - 1)); the products of these limits over the nonconstant modes are log H_3 and log H_i, and the constant modes contribute the coefficient (n - 2)/(2n) of log a.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.GM3_eq_fourierGM`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.cycle_gram_det`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.one_sub_tripartiteEigenvalue`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.residualConstant`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.residual_determinant_limit`
- Truth anchor: `D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.tripartite_gram_det`
- Dependency: [D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic](../GaussianMultiEntropyAsymptotic.md)
