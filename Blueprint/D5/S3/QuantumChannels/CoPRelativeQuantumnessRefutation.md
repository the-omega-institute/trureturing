# Relative quantumness can increase under a commutativity-preserving channel

## Abstract

A completely positive, trace-preserving qubit channel that preserves commuting density matrices increases relative quantumness at alpha zero. The exact trace arguments of the logarithms are 50401283/7340144 before the channel and 1879639/266240 afterwards.

**Definition 1.1 (Density matrices).**

$$\forall d : \mathbb{N}, \forall A : \mathbb{C}^{d\times d}, \operatorname{IsDensity}\left(A\right) \Leftrightarrow ((\operatorname{PSD}\left(A\right)) \land (\operatorname{Tr}\left(A\right) = 1))$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

A density matrix on C^d is a positive semidefinite complex d by d matrix with trace one. PSD denotes Matrix.PosSemidef and Tr is the complex matrix trace.

**Definition 1.2 (Regularization).**

$$\forall d : \mathbb{N}, \forall \varepsilon : \mathbb{R}, \forall A : \mathbb{C}^{d\times d}, \operatorname{reg}\left(\varepsilon, A\right) = (1 - \varepsilon) \cdot A + \frac{\varepsilon}{\operatorname{real}\left(d\right)} \cdot I$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.reg` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Given $\rho,\sigma\in\mathcal{D}\left(\mathcal{H}\right)$ and a parameter $\varepsilon\in(0,1)$, define $\rho_{\varepsilon}:=(1 - \varepsilon)\rho+\varepsilon\frac{\mathbb{I}}{d},\quad\sigma_{\varepsilon}:=(1 - \varepsilon)\sigma+\varepsilon\frac{\mathbb{I}}{d}$, where $d = \operatorname{dim}\left(\mathcal{H}\right)$. Here d is a natural number, A is a complex d by d matrix, and epsilon is real. The division epsilon/d is real division after casting d to the reals; I is the identity matrix and scalar multiplication is by a real scalar. The conjecture uses 0 < epsilon < 1.

**Definition 1.3 (Relative quantumness at alpha zero).**

$$\forall d : \mathbb{N}, \forall A : \mathbb{C}^{d\times d}, \forall B : \mathbb{C}^{d\times d}, \operatorname{Q}\left(A, B\right) = -(\frac{1}{(0 - 1)} \cdot \operatorname{ln}\left(\operatorname{Re}\left(\operatorname{Tr}\left(A \cdot \operatorname{exp}\left((0 - 1) \cdot (\operatorname{log}\left(A\right) - \operatorname{log}\left(B\right))\right)\right)\right)\right))$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.Q` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Define $Q\left(\rho_{\varepsilon}\Vert\sigma_{\varepsilon}\right):=-S_{0}^{Q}\left(\rho_{\varepsilon}\Vert\sigma_{\varepsilon}\right)$. The expression displayed here is literally minus S_0^Q, with the source factor 1/(0-1) and exponent (0-1)(log A-log B). Log of a matrix means continuous functional calculus for the real logarithm in the L2 operator norm; exp is the matrix exponential. The scalar logarithm is applied to the real part of the complex trace. On the positive definite matrices used below that trace is the positive real number calculated explicitly.

**Definition 1.4 (Completely positive trace-preserving maps).**

$$\forall d : \mathbb{N}, \forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsCPTP}\left(N\right) \Leftrightarrow ((\operatorname{IsCompletelyPositive}\left(N\right)) \land (\forall A : \mathbb{C}^{d\times d}, \operatorname{Tr}\left(N\left(A\right)\right) = \operatorname{Tr}\left(A\right)))$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

MatrixMap(Fin(d), Fin(d), C) is the type of complex-linear maps between d by d complex matrices. IsCompletelyPositive is the existing matrix-map predicate: every amplification by an identity map preserves positive semidefiniteness. Trace preservation is quantified over all complex matrices A, without a density-matrix restriction.

**Definition 1.5 (Preservation of commuting density matrices).**

$$\forall d : \mathbb{N}, \forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsCoP}\left(N\right) \Leftrightarrow (\forall A : \mathbb{C}^{d\times d}, \forall B : \mathbb{C}^{d\times d}, (\operatorname{IsDensity}\left(A\right)) \Rightarrow ((\operatorname{IsDensity}\left(B\right)) \Rightarrow ((A \cdot B = B \cdot A) \Rightarrow (N\left(A\right) \cdot N\left(B\right) = N\left(B\right) \cdot N\left(A\right)))))$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCoP` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Let $\mathcal{H}$ be a finite-dimensional Hilbert space. A CPTP map $\mathcal{N}:\mathcal{B}\left(\mathcal{H}\right)\to\mathcal{B}\left(\mathcal{H}\right)$ is called a CoP channel if, for every pair $(\rho,\sigma)\in\mathcal{D}\left(\mathcal{H}\right)\times\mathcal{D}\left(\mathcal{H}\right)$ satisfying $[\rho,\sigma] = 0$, one has $[\mathcal{N}\left(\rho\right),\mathcal{N}\left(\sigma\right)] = 0$. (Section VIII.A, PDF p. 18.) The predicate IsCoP encodes the commuting-pair condition; the separate IsCPTP premise supplies the CPTP requirement in the quoted definition. Equality AB = BA encodes the vanishing commutator. Both A and B range over all complex d by d matrices and are required to be density matrices.

**Definition 1.6 (Matrix support).**

$$\forall d : \mathbb{N}, \forall A : \mathbb{C}^{d\times d}, \operatorname{supp}\left(A\right) = \operatorname{range}\left(\operatorname{toLin}'\left(A\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.supp` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

The support of A is the range of the linear map Matrix.toLin' A on C^d, with the standard coordinate basis. For Hermitian positive semidefinite matrices this is the usual operator support. Inclusion of supports is the submodule order, written as subset inclusion.

**Definition 1.7 (Conjecture 15).**

$$claim \Leftrightarrow (\forall d : \mathbb{N}, \forall \rho : \mathbb{C}^{d\times d}, \forall \sigma : \mathbb{C}^{d\times d}, \forall \varepsilon : \mathbb{R}, \forall N : \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), (\operatorname{IsDensity}\left(\rho\right)) \Rightarrow ((\operatorname{IsDensity}\left(\sigma\right)) \Rightarrow ((\rho \cdot \sigma \ne \sigma \cdot \rho) \Rightarrow ((0 < \varepsilon) \Rightarrow ((\varepsilon < 1) \Rightarrow ((\operatorname{IsCPTP}\left(N\right)) \Rightarrow ((\operatorname{IsCoP}\left(N\right)) \Rightarrow ((\operatorname{supp}\left(N\left(\operatorname{reg}\left(\varepsilon, \rho\right)\right)\right) \subseteq \operatorname{supp}\left(N\left(\operatorname{reg}\left(\varepsilon, \sigma\right)\right)\right)) \Rightarrow ((\operatorname{Q}\left(N\left(\operatorname{reg}\left(\varepsilon, \rho\right)\right), N\left(\operatorname{reg}\left(\varepsilon, \sigma\right)\right)\right) \le \operatorname{Q}\left(\operatorname{reg}\left(\varepsilon, \rho\right), \operatorname{reg}\left(\varepsilon, \sigma\right)\right)) \land (0 \le \operatorname{Q}\left(N\left(\operatorname{reg}\left(\varepsilon, \rho\right)\right), N\left(\operatorname{reg}\left(\varepsilon, \sigma\right)\right)\right)))))))))))$$

*Formalization.* `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.claim` (`✓ std3`).

*Citation.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

\begin{conjecture}[QDPI at $\alpha = 0$ for non-commuting inputs under CoP channels] Let $(\rho,\sigma)\in\mathcal{D}\left(\mathcal{H}\right)\times\mathcal{D}\left(\mathcal{H}\right)$ satisfy $[\rho,\sigma] \ne 0,$ where $\rho_{\varepsilon},\sigma_{\varepsilon}$ are the regularized states defined in Eq.\eqref{state_regularized}. Suppose that $\mathcal{N}$ is a CoP channel satisfying $\operatorname{supp}\left(\mathcal{N}\left(\rho_{\varepsilon}\right)\right) \subseteq \operatorname{supp}\left(\mathcal{N}\left(\sigma_{\varepsilon}\right)\right). $ Then, \begin{equation} $Q\left(\rho_{\varepsilon}\Vert\sigma_{\varepsilon}\right)\geq Q\left(\mathcal{N}\left(\rho_{\varepsilon}\right)\Vert\mathcal{N}\left(\sigma_{\varepsilon}\right)\right)\geq 0.$ \end{equation} \end{conjecture} (Conjecture 15, Section VIII.A, PDF p. 18.) Here H is C^d for arbitrary natural d; rho and sigma are density matrices; epsilon is real with 0 < epsilon < 1; and N is a complex-linear map satisfying IsCPTP and IsCoP. The source nonzero commutator is rho sigma and sigma rho differ. Rho_epsilon and sigma_epsilon are reg(epsilon,rho) and reg(epsilon,sigma). Support inclusion is inclusion of their output ranges. The two conclusion inequalities are encoded as Q(output rho,output sigma) <= Q(input rho,input sigma) and 0 <= Q(output rho,output sigma). The displayed pair normalizes the source typo. Verbatim malformed source fragment: \rho,\sigma)\in \mathcal D(\mathcal H)\times\mathcal D(\mathcal H).

**Theorem 1.8 (A qubit refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Meunson; T. Deesuwan (2026). *Cumulant-based quantum relative Rényi functional*. DOI: [10.48550/arXiv.2606.31205](https://doi.org/10.48550/arXiv.2606.31205). URL: <https://arxiv.org/abs/2606.31205v1>.

*Commentary.*

Put t_n = (4^n-1)/(4^n+1), R = (I+t_7 Z)/2, S = (I+t_8 H)/2, R' = (I+t_6 Z)/2 and S' = (I+t_3 J)/2, where X and Z are Pauli matrices, H = (11 Z+5 sqrt(3) X)/14 and J = (29 Z+sqrt(455) X)/36. Set epsilon = 1/65537 and recover rho and sigma from R and S by undoing regularization. The unital channel has N(X) = u X+v Z, N(Y) = u w Y and N(Z) = w Z, with u = (3211313/127793250) sqrt(1365), v = -(727356123473/168188824118250) sqrt(3), w = 22365525/22373717. Four explicit Kraus operators realize the channel: reshape the vectors bp(v/a), ep, bm(v/b), em in output-input index order and scale them by sqrt(a/4), sqrt(delta/(4a)), sqrt(b/4), sqrt(delta/(4b)), where a=(1+u)(1+w), b=(1-u)(1+w) and delta=(1-u^2)(1-w^2)-v^2. Entrywise equality to the Kraus sum proves complete positivity using the frozen Kraus-channel theorem; its trace is preserved on every input. Entrywise commutator identities show preservation of every commuting pair. The inputs are noncommuting density matrices, and both outputs are positive definite, so the support inclusion holds. Two-point functional calculus for self-adjoint involutions gives Tr[R exp(log S-log R)] = 50401283/7340144 < 1879639/266240 = Tr[R' exp(log S'-log R')]. Strict monotonicity of the real logarithm contradicts the first inequality of Conjecture 15.

## References

- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCoP`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsDensity`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.Q`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.reg`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.supp`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Quantum/Foundation/FiniteKrausChannel.md)
