# Unital-block overlap can be less than minus one

## Abstract

Two completely positive trace-preserving qutrit maps have unital-block overlap minus four thirds, contradicting the proposed lower bound of minus one.

**Definition 1.1 (Liouville operator bases).**

$$\forall (d: \mathbb{N}), \forall (X: \operatorname{Fin}\left(d^{2}\right)\to\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (h0: 0 < d^{2}), \operatorname{IsLiouvilleBasis}\left(X, h0\right) \Leftrightarrow ((\forall (mu: \operatorname{Fin}\left(d^{2}\right)), \forall (nu: \operatorname{Fin}\left(d^{2}\right)), \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\left(mu\right)\right) \cdot X\left(nu\right)\right) = \operatorname{ite}\left(mu = nu, 1, 0\right)) \land (X\left(\operatorname{Fin}.\operatorname{mk}\left(0, h0\right)\right) = (\operatorname{Real}.\operatorname{sqrt}\left((d:\mathbb{R})\right):\mathbb{C})^{-1} \cdot 1))$$

*Formalization.* `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.IsLiouvilleBasis` (`✓ std3`).

*Citation.* Matthew Girling, Cristina Cîrstoiu, and David Jennings (2022). *Estimation of correlations and non-separability in quantum channels via unitarity benchmarking*. DOI: [10.1103/PhysRevResearch.4.023041](https://doi.org/10.1103/PhysRevResearch.4.023041). URL: <https://arxiv.org/abs/2104.04352>.

*Commentary.*

We choose an orthonormal basis of operators X₀, X₁, …, X_{d²−1} for B(H_A) with X₀ = 1/√d and with respect to the Hilbert Schmidt inner product ⟨X_μ, X_ν⟩ := tr X_μ†X_ν = δ_{μ,ν}. In particular, this means that X₁, …, X_{d²−1} are all traceless operators. (Section II.C, arXiv v3 PDF p. 5.) The dimension d is natural, the operator indices are Fin(d^2), and h0 proves that index zero exists. The first condition is complex Hilbert-Schmidt orthonormality; the second fixes the normalized identity. The square root takes the real cast of d and is then cast to the complex numbers.

**Definition 1.2 (Liouville entries).**

$$\forall (d: \mathbb{N}), \forall (Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (X: \operatorname{Fin}\left(d^{2}\right)\to\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (i: \operatorname{Fin}\left(d^{2}\right)), \forall (j: \operatorname{Fin}\left(d^{2}\right)), \operatorname{unitalBlock}\left(Phi, X, i, j\right) = \operatorname{Matrix}.\operatorname{trace}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(X\left(i\right)\right) \cdot Phi\left(X\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.unitalBlock` (`✓ std3`).

*Citation.* Matthew Girling, Cristina Cîrstoiu, and David Jennings (2022). *Estimation of correlations and non-separability in quantum channels via unitarity benchmarking*. DOI: [10.1103/PhysRevResearch.4.023041](https://doi.org/10.1103/PhysRevResearch.4.023041). URL: <https://arxiv.org/abs/2104.04352>.

*Commentary.*

Section II.C, arXiv v3 PDF p. 5, gives the Liouville entries as the trace of X_i conjugate-transposed times the channel image of X_j. The function is defined on all indices; its restriction to positive i and j is the unital block. MatrixMap is the complex-linear matrix-map type. Matrix.conjTranspose and Matrix.trace are the matrix adjoint and trace.

**Definition 1.3 (Overlap of the unital blocks).**

$$\forall (d: \mathbb{N}), \forall (Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (Psi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (X: \operatorname{Fin}\left(d^{2}\right)\to\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \operatorname{overlap}\left(Phi, Psi, X\right) = \sum_{i: \operatorname{Fin}\left(d^{2}\right)} (\sum_{j: \operatorname{Fin}\left(d^{2}\right)} (\operatorname{ite}\left((\operatorname{val}\left(i\right) \ne 0) \land (\operatorname{val}\left(j\right) \ne 0), \operatorname{star}\left(\operatorname{unitalBlock}\left(Phi, X, i, j\right)\right) \cdot \operatorname{unitalBlock}\left(Psi, X, i, j\right), 0\right)))$$

*Formalization.* `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.overlap` (`✓ std3`).

*Citation.* Matthew Girling, Cristina Cîrstoiu, and David Jennings (2022). *Estimation of correlations and non-separability in quantum channels via unitarity benchmarking*. DOI: [10.1103/PhysRevResearch.4.023041](https://doi.org/10.1103/PhysRevResearch.4.023041). URL: <https://arxiv.org/abs/2104.04352>.

*Commentary.*

The overlap in Appendix C.5 is the Hilbert-Schmidt inner product of the two unital blocks. The double sum includes only indices with nonzero Fin.val. Each summand is the complex conjugate of the first Liouville entry multiplied by the second entry; star denotes complex conjugation. No division of natural numbers occurs.

**Definition 1.4 (The proposed universal lower bound).**

$$claim \Leftrightarrow (\forall (d: \mathbb{N}), \forall (h0: 0 < d^{2}), \forall (Phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (Psi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), \forall (X: \operatorname{Fin}\left(d^{2}\right)\to\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Phi\right)) \Rightarrow ((\operatorname{CoPRelativeQuantumnessRefutation}.\operatorname{IsCPTP}\left(Psi\right)) \Rightarrow ((\operatorname{IsLiouvilleBasis}\left(X, h0\right)) \Rightarrow (-1 \le (\operatorname{overlap}\left(Phi, Psi, X\right)).\operatorname{re}))))$$

*Formalization.* `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.claim` (`✓ std3`).

*Citation.* Matthew Girling, Cristina Cîrstoiu, and David Jennings (2022). *Estimation of correlations and non-separability in quantum channels via unitarity benchmarking*. DOI: [10.1103/PhysRevResearch.4.023041](https://doi.org/10.1103/PhysRevResearch.4.023041). URL: <https://arxiv.org/abs/2104.04352>.

*Commentary.*

However, we conjecture a stronger result that for any two quantum channels E₁, E₂ that ⟨T₁, T₂⟩ ≥ −1. (Appendix C.5, after Lemma C.3, arXiv v3 PDF p. 21.) The paper also states: Since it is not essential to our work we leave it as an open problem. Here Phi and Psi range over all complex-linear maps on d by d matrices, and CoPRelativeQuantumnessRefutation.IsCPTP requires complete positivity and trace preservation on all matrices. The basis satisfies IsLiouvilleBasis. The comparison uses the real part of the complex overlap, agreeing with the source inner product for Hermitian operator bases.

**Theorem 1.5 (Two qutrit coarse-graining channels).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/girling-cirstoiu-jennings-2022-unital-block-overlap` (refuted) by `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"girling-cirstoiu-jennings-2022-unital-block-overlap","declaration_gid":"D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthew Girling, Cristina Cîrstoiu, and David Jennings (2022). *Estimation of correlations and non-separability in quantum channels via unitarity benchmarking*. DOI: [10.1103/PhysRevResearch.4.023041](https://doi.org/10.1103/PhysRevResearch.4.023041). URL: <https://arxiv.org/abs/2104.04352>.

*Commentary.*

Use the Kraus families (E00, E01, E12) and (E10, E11, E02), with Eij = Matrix.single i j 1. The first channel sends a matrix A to diagonal(A00+A11, A22, 0); the second sends it to diagonal(A22, A00+A11, 0). Each Kraus representation proves complete positivity, and FiniteKrausChannel.finite_kraus_quantum_channel supplies trace preservation because each sum of adjoint Kraus products is the identity. Choose the nine Hermitian operators I/sqrt(3), diagonal(1,-1,0)/sqrt(2), diagonal(1,1,-2)/sqrt(6), and the symmetric and imaginary antisymmetric matrix units for the three off-diagonal pairs, each divided by sqrt(2). Their eighty-one inner products give an orthonormal basis. On the eight traceless operators both channels have just one nonzero Liouville entry, at row one and column two, with values 4/(sqrt(2) sqrt(6)) and its negative. Their overlap is therefore minus four thirds, strictly below minus one. Neither channel is unital, and dimension three lies outside the qubit case of Lemma C.4.

## References

- Truth anchor: `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.IsLiouvilleBasis`
- Truth anchor: `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.claim`
- Truth anchor: `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.overlap`
- Truth anchor: `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.result`
- Truth anchor: `D5/S3/QuantumChannels/UnitalBlockOverlapRefutation.unitalBlock`
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Algebra/CStarSmaleHigherOrder](../Quantum/Algebra/CStarSmaleHigherOrder.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](CoPRelativeQuantumnessRefutation.md)
