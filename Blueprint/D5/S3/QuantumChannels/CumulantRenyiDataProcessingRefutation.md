# Data processing fails for the cumulant-based Renyi functional at every order above one

## Abstract

Meunson and Deesuwan (arXiv:2606.31205) define a cumulant-based quantum relative Renyi functional for alpha > 1 and state in the abstract and conclusion that its quantum data-processing inequality under arbitrary CPTP maps remains open. For every alpha > 1 a pair of positive definite qubit states and the complete dephasing channel increase the functional, so the inequality fails at every order above one.

**Definition 1.1 (The cumulant-based relative Renyi functional).**

$$\forall d : \mathbb{N}, \forall \alpha : \mathbb{R}, \forall A : \mathbb{C}^{d\times d}, \forall B : \mathbb{C}^{d\times d}, \operatorname{cuRenyi}\left(\alpha, A, B\right) = \frac{1}{(\alpha - 1)} \cdot \operatorname{ln}\left(\operatorname{Re}\left(\operatorname{Tr}\left(A \cdot \operatorname{exp}\left((\alpha - 1) \cdot (\operatorname{log}\left(A\right) - \operatorname{log}\left(B\right))\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.cuRenyi` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Definition 3 of the paper, on faithful inputs: for complex d by d matrices A and B and real alpha, the value is 1/(alpha-1) times the real logarithm of the real part of Tr(A exp((alpha-1)(log A - log B))). Log of a matrix is continuous functional calculus for the real logarithm and exp is the matrix exponential, as in the frozen alpha-zero refutation for the same paper. On positive definite A and B the trace is a positive real number, and the formula is the paper's.

**Definition 1.2 (The data-processing inequality at alpha).**

$$\forall \alpha : \mathbb{R}, \operatorname{QDPI}\left(\alpha\right) \Leftrightarrow (\forall d : \mathbb{N}, \forall \rho : \mathbb{C}^{d\times d}, \forall \sigma : \mathbb{C}^{d\times d}, \forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow ((\operatorname{PosDef}\left(\rho\right)) \Rightarrow ((\operatorname{PosDef}\left(\sigma\right)) \Rightarrow ((\operatorname{IsCPTP}\left(N\right)) \Rightarrow ((\operatorname{PosDef}\left(N\left(\rho\right)\right)) \Rightarrow ((\operatorname{PosDef}\left(N\left(\sigma\right)\right)) \Rightarrow (\operatorname{cuRenyi}\left(\alpha, N\left(\rho\right), N\left(\sigma\right)\right) \le \operatorname{cuRenyi}\left(\alpha, \rho, \sigma\right)))))))))$$

*Formalization.* `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.QDPI` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Section III of the paper states data processing as S_alpha(rho||sigma) >= S_alpha(N(rho)||N(sigma)) for every CPTP map N and states with supp(rho) contained in supp(sigma). QDPI(alpha) states it for density matrices rho and sigma on C^d of every dimension d that are positive definite, for every CPTP map N on d by d complex matrices with positive definite outputs. IsDensity and IsCPTP are the frozen definitions of the alpha-zero refutation for the same paper. Faithful inputs satisfy the support condition, and faithful outputs need no convention for the logarithm of a singular matrix.

**Definition 1.3 (Data processing for some order above one).**

$$claim \Leftrightarrow (\exists \alpha : \mathbb{R}, (1 < \alpha) \land (\operatorname{QDPI}\left(\alpha\right)))$$

*Formalization.* `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

The open question of the abstract and conclusion, in its weakest form: some alpha > 1 satisfies QDPI(alpha). Its negation refutes data processing at every order above one, already for faithful inputs and outputs.

**Theorem 1.4 (No order above one satisfies data processing).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/meunson-deesuwan-2026-cumulant-renyi-qdpi` (refuted) by `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meunson-deesuwan-2026-cumulant-renyi-qdpi","declaration_gid":"D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Fix alpha > 1, put t = alpha - 1, x = 16^(1 + 1/t), r = (x - 1)/(x + 1) and a = (ln x)/2. Let N be the symmetric involution with rows (1/2, sqrt(3)/2) and (sqrt(3)/2, -1/2), and Z = diag(1, -1); then B = N - Z is also a self-adjoint involution. The states rho = (I + r N)/2 and sigma = (I + r Z)/2 are positive definite with trace one and common spectrum {x/(x+1), 1/(x+1)}. Two-point functional calculus gives log rho - log sigma = a B and exp(t a B) = cosh(t a) I + sinh(t a) B, so the input trace is cosh(t a) + (r/2) sinh(t a), which is less than exp(t a) = 4^(t+1). The complete dephasing channel with Kraus operators diag(1, 0) and diag(0, 1) is CPTP and sends rho and sigma to the positive definite diagonal matrices diag(p+, p-) and diag(q+, q-) with p- = (x+3)/(4(x+1)) > 1/4 and q- = 1/(x+1). The output trace is p+^(t+1) q+^(-t) + p-^(t+1) q-^(-t) > (1/4) ((x+3)/4)^t > (1/4) (x/4)^t = 4^(t+1). By strict monotonicity of the logarithm and 1/t > 0 the functional increases under the channel, contradicting QDPI(alpha).

## References

- Truth anchor: `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.QDPI`
- Truth anchor: `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.cuRenyi`
- Truth anchor: `D5/S3/QuantumChannels/CumulantRenyiDataProcessingRefutation.result`
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
