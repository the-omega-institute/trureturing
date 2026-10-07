# Bourin–Lee Conjecture 3.3

## Abstract

For every n >= 1, the Euclidean operator-norm inequality for all positive block completions forces the off-diagonal complex n-by-n matrix to be essentially Hermitian. No invertibility or distinct-singular-value assumption is required.

**Definition 1.1 (Essentially Hermitian matrices).**

$$\forall (n : \mathbb{N}), \forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{EssentiallyHermitian}\left(X\right) = (\exists (\alpha : \mathbb{C}), \exists (\beta : \mathbb{C}), \exists (H : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{IsHermitian}\left(H\right)) \land (X = \alpha \cdot H + \beta \cdot 1))$$

*Formalization.* `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.EssentiallyHermitian` (`✓ std3`).

*Citation.* J.-C. Bourin and E.-Y. Lee (2021). *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*. DOI: [10.1142/S0129167X22500094](https://doi.org/10.1142/S0129167X22500094). URL: <https://arxiv.org/abs/2111.15180v1>.

*Commentary.*

Printed page 6, verbatim: "If W(T) is line segment, then T is a so-called essentially Hermitian matrix." The affine Hermitian expression fixed for this notion is X = α • H + β • 1, where α and β are complex and H is Hermitian. A point is allowed, including α = 0.

**Definition 1.2 (All positive block completions).**

$$\forall (n : \mathbb{N}), \forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \operatorname{CompletionBound}\left(X\right) = (\forall (A : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (B : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{Matrix}.\operatorname{fromBlocks}\left(A, X, \operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right), B\right)\right)) \Rightarrow (\left\lVert \operatorname{Matrix}.\operatorname{fromBlocks}\left(A, X, \operatorname{Matrix}.\operatorname{conjTranspose}\left(X\right), B\right) \right\rVert \le \left\lVert A + B \right\rVert))$$

*Formalization.* `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.CompletionBound` (`✓ std3`).

*Citation.* J.-C. Bourin and E.-Y. Lee (2021). *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*. DOI: [10.1142/S0129167X22500094](https://doi.org/10.1142/S0129167X22500094). URL: <https://arxiv.org/abs/2111.15180v1>.

*Commentary.*

The displayed hypothesis in Conjecture 3.3 uses Matrix.fromBlocks A X (Matrix.conjTranspose X) B and Matrix.PosSemidef. Both norms are the Euclidean operator norm: Matrix.Norms.L2Operator, definitionally the norm of Matrix.toEuclideanCLM. A and B range over all complex n-by-n matrices; positivity supplies their Hermitian and positive properties.

**Definition 1.3 (Conjecture 3.3).**

$$claim = (\forall (n : \mathbb{N}), (1 \le n) \Rightarrow (\forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{CompletionBound}\left(X\right)) \Rightarrow (\operatorname{EssentiallyHermitian}\left(X\right))))$$

*Formalization.* `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.claim` (`✓ std3`).

*Citation.* J.-C. Bourin and E.-Y. Lee (2021). *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*. DOI: [10.1142/S0129167X22500094](https://doi.org/10.1142/S0129167X22500094). URL: <https://arxiv.org/abs/2111.15180v1>.

*Commentary.*

Printed page 6, Conjecture 3.3, verbatim: "Let $X \in \mathbb{M}_{n}$. If the inequality $\left\lVert \begin{bmatrix}A&X\\X^{*}&B\end{bmatrix} \right\rVert_{\infty} \le \left\lVert A + B \right\rVert_{\infty}$ holds for all positive block-matrix with $X$ as off-diagonal block, then $X$ is essentially Hermitian."

The source's 2-by-2 array has n-by-n complex matrix blocks, and its X* denotes Matrix.conjTranspose X. The Lean sentence explicitly quantifies every natural n >= 1 and every X; the positivity, universal completion quantifier and affine Hermitian conclusion are encoded by the two preceding definitions.

**Theorem 1.4 (The conjecture holds in every positive dimension).**

$$\forall (n : \mathbb{N}), (1 \le n) \Rightarrow (\forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{CompletionBound}\left(X\right)) \Rightarrow (\operatorname{EssentiallyHermitian}\left(X\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J.-C. Bourin and E.-Y. Lee (2021). *Eigenvalue inequalities for positive block matrices with the inradius of the numerical range*. DOI: [10.1142/S0129167X22500094](https://doi.org/10.1142/S0129167X22500094). URL: <https://arxiv.org/abs/2111.15180v1>.

*Commentary.*

Positive scalar shifts make the two real spectral edges of K X D sum to zero for every Hermitian D. The quantitative rank-one spike estimate forces first normality and then equality of the projected rank-one matrices. A normal matrix with this equality has collinear eigenvalues; unitary diagonalization reconstructs an affine Hermitian expression. The private diagonalization proof is adapted from TauCeti under Apache-2.0, as detailed in the cited note.

## References

- Truth anchor: `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.CompletionBound`
- Truth anchor: `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.EssentiallyHermitian`
- Truth anchor: `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.claim`
- Truth anchor: `D5/S3/Quantum/BlockNorm/EssentiallyHermitian.result`
- Dependency: [D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate](SpikeEdgeEstimate.md)
