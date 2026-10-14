# The sharp local-perception CHSH bound

## Abstract

The termwise local-perception CHSH sum has sharp upper bound two for all two-qubit states and dichotomic settings.

**Definition 1.1 (Dichotomic observables).**

$$\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.IsDichotomic}\left(A\right)) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left((1 + A)\right)) \land (\operatorname{Matrix.PosSemidef}\left((1 - A)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.IsDichotomic` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The dichotomic positive-operator-valued measurement condition is positivity of both identity plus A and identity minus A. Dividing these matrices by two gives the effects for the two outcomes. Matrix.PosSemidef includes Hermiticity over the complex numbers, so this condition describes Hermitian contractions and includes projective observables with outcomes plus and minus one.

**Definition 1.2 (Alice's local mean).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.meanA}\left(rho, A\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot \operatorname{Matrix.kronecker}\left(A, 1\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.meanA` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

Equations (5) and (10) give Alice's mean as the trace against her reduced state. Equivalently, it is the real part of Matrix.trace of the bipartite state times the Kronecker product of Alice's observable with the identity on Bob's factor.

**Definition 1.3 (Bob's local mean).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.meanB}\left(rho, B\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot \operatorname{Matrix.kronecker}\left(1, B\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.meanB` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

Equations (5) and (10) give Bob's mean as the trace against his reduced state. Equivalently, it is the real part of Matrix.trace of the bipartite state times the Kronecker product of the identity on Alice's factor with Bob's observable.

**Definition 1.4 (The bipartite correlator).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.correl}\left(rho, A, B\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(rho \cdot \operatorname{Matrix.kronecker}\left(A, B\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.correl` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

Equation (11) gives the correlator as the trace of the state times the Kronecker product of the two observables. Taking Complex.re defines a real number for every complex matrix; for a density matrix and Hermitian observables, the trace is already real.

**Definition 1.5 (The CHSH coefficient table).**

$$\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.chshCoeff} = [[1, 1], [1, -1]]$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.chshCoeff` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

Equation (19) uses two settings on each side. The coefficient is one for the first three pairs and minus one when both settings have index one. The marginal coefficients vanish.

**Definition 1.6 (The termwise local-perception sum).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall A \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; \forall B \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.lpoCHSH}\left(rho, A, B\right) = \sum_{x: \operatorname{Fin}\left(2\right)} (\sum_{y: \operatorname{Fin}\left(2\right)} (\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.chshCoeff}\left(x, y\right) \cdot \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.meanA}\left(rho, A\left(x\right)\right) \cdot \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.meanB}\left(rho, B\left(y\right)\right) \cdot \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.correl}\left(rho, A\left(x\right), B\left(y\right)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.lpoCHSH` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

This is the termwise sum in the second line of Equation (21), with the CHSH coefficients of Equation (19). Equation (35) identifies each local-perception correlator with the product of the two local means and the ordinary correlator, so summing these correlators with the CHSH coefficients gives the same expression. The bound concerns this termwise functional. The first line of Equation (21), the expectation of the tensor product of the two perceived Bell operators, contains cross terms between different settings and gives four for the state |00⟩ with σ_z at every setting.

**Definition 1.7 (The bound two is attained).**

$$(\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.claim}) \Leftrightarrow ((\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho\right) = 1) \Rightarrow (\forall A \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; \forall B \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; (\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.IsDichotomic}\left(A\left(x\right)\right)) \Rightarrow ((\forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.IsDichotomic}\left(B\left(y\right)\right)) \Rightarrow (\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.lpoCHSH}\left(rho, A, B\right) \le 2))))) \land (\exists rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \exists A \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; \exists B \in (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)),\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \land ((\operatorname{Matrix.trace}\left(rho\right) = 1) \land ((\forall x \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.IsDichotomic}\left(A\left(x\right)\right)) \land ((\forall y \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.IsDichotomic}\left(B\left(y\right)\right)) \land (\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.lpoCHSH}\left(rho, A, B\right) = 2))))))$$

*Formalization.* `D5/S3/QuantumBounds/LocalPerceptionCHSH.claim` (`✓ std3`).

*Citation.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

The conjecture after Equation (31) asks whether the upper bound two persists for arbitrary settings. The first clause states the bound for every positive-semidefinite two-qubit state of trace one and every pair of dichotomic settings on each side, without an orthogonality assumption. The second clause states that some such state and settings attain two. Together they say that the largest termwise value over all states and settings is exactly two.

**Theorem 1.8 (The sharp bound holds for all settings).**

$$\operatorname{D5.S3.QuantumBounds.LocalPerceptionCHSH.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/LocalPerceptionCHSH.result` (`✓ std3`). ∎

*Resolves.* `Problems/ray-2025-local-perception-chsh-bound` (proved) by `D5/S3/QuantumBounds/LocalPerceptionCHSH.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ray-2025-local-perception-chsh-bound","declaration_gid":"D5/S3/QuantumBounds/LocalPerceptionCHSH.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rohit Kishan Ray (2025). *Local perception operators and classicality: new tools for old tests*. DOI: [10.48550/arXiv.2511.00314](https://doi.org/10.48550/arXiv.2511.00314). URL: <https://arxiv.org/abs/2511.00314v1>.

*Commentary.*

For outcome signs epsilon and eta equal to plus or minus one, the local effects are (1 + epsilon A)/2 and (1 + eta B)/2. Their Kronecker product is positive semidefinite. Its expectation in a positive-semidefinite state of trace one is nonnegative and expands to (1 + epsilon a + eta b + epsilon eta C)/4.

Relabeling either local outcome changes the signs of its mean and the corresponding correlators, preserving every product of the two means and the correlator. Thus the four means p, q, r, s may be taken in the interval from zero to one. The positivity inequalities give C00 at most one, C01 at most 1 - p + s, C10 at most 1 + q - r, and C11 at least q + s - 1. Multiplication by the nonnegative local means bounds the sum by G = pr + ps(1 - p + s) + qr(1 + q - r) + qs(1 - q - s).

The polynomial identity 2 - G = ((1 - p)/2)(r + s² + (1 - s)²) + s(1 - p)² + ((1 - r)/2)(p + q² + (1 - q)²) + q(1 - r)² + (1 - q)(1 - s)(1 + q + s) expresses the difference as a sum of nonnegative terms. This proves the upper bound two. The state |00⟩⟨00| with σ_z at every setting has all means and correlators equal to one, so its termwise sum is two and attains the bound.

## References

- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.IsDichotomic`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.chshCoeff`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.claim`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.correl`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.lpoCHSH`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.meanA`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.meanB`
- Truth anchor: `D5/S3/QuantumBounds/LocalPerceptionCHSH.result`
