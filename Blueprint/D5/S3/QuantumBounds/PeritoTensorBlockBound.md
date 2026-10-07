# Unitary spectral blocks and the tensor bound

## Abstract

Unitary tensor sums satisfy the uniform scalar coefficient bound on the unit circle in the Euclidean operator norm, for all finite dimensions and all finite numbers of summands.

All matrix norms below are operator norms for the Euclidean vector norm. The local spaces have dimensions n and m, and the summation index is Fin d. The dimensions and d may be zero. The symbol kronecker denotes the matrix tensor product, and unitaryGroup is the group of complex matrices whose conjugate transpose is their inverse.

**Theorem 1.1 (Uniform diagonal block bound).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (d : \mathbb{N}), \forall (c : (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(n\right) \to \mathbb{C}))), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))), \forall (K : \mathbb{R}), (\forall (y : \operatorname{Fin}\left(d\right)), B\left(y\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(m\right), \mathbb{C}\right)) \Rightarrow ((0 \le K) \Rightarrow ((\forall (i : \operatorname{Fin}\left(n\right)), \sum_{y \in \operatorname{Fin}\left(d\right)} \left\lVert c\left(y\right)\left(i\right) \right\rVert \le K) \Rightarrow (\left\lVert \sum_{y \in \operatorname{Fin}\left(d\right)} \operatorname{kronecker}\left(\operatorname{diagonal}\left(c\left(y\right)\right), B\left(y\right)\right) \right\rVert \le K)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTensorBlockBound.norm_diagonal_tensor_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be a complex coefficient array and let every B(y) be unitary. Suppose K is nonnegative and, for every i, the sum of the moduli of c(y)(i) is at most K. The tensor sum of diagonal(c(y)) with B(y) then has operator norm at most K.

Write a vector as Bob-vector rows v(i). The i-th output row is the sum of c(y)(i) times B(y)v(i). The triangle inequality and unitary norm preservation bound its norm by K times the norm of v(i). Summing the squared row norms bounds the squared total norm by K squared times the squared input norm. Nonnegativity of K permits taking square roots.

**Theorem 1.2 (Unit-circle bound for a unitary tensor sum).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (d : \mathbb{N}), \forall (U : \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), \forall (B : (\operatorname{Fin}\left(d\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right))), \forall (K : \mathbb{R}), (U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)) \Rightarrow ((\forall (y : \operatorname{Fin}\left(d\right)), B\left(y\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(m\right), \mathbb{C}\right)) \Rightarrow ((\forall (z : \mathbb{C}), (\left\lVert z \right\rVert = 1) \Rightarrow (\sum_{y \in \operatorname{Fin}\left(d\right)} \left\lVert 1 + \operatorname{windowRoot}\left(d\right)^{y} \cdot z \right\rVert \le K)) \Rightarrow (\left\lVert \sum_{y \in \operatorname{Fin}\left(d\right)} \operatorname{kronecker}\left(1 + \operatorname{windowRoot}\left(d\right)^{y} \cdot U, B\left(y\right)\right) \right\rVert \le K)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoTensorBlockBound.tensor_block_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, the phase windowRoot(d) is exp(2 pi i/d); for d = 0 the sum is empty. If U and all B(y) are unitary, and the sum of |1 + windowRoot(d)^y z| is at most K for every complex z of modulus one, the tensor sum of I + windowRoot(d)^y U with B(y) has operator norm at most K. The scalar hypothesis at z = 1 already implies K is nonnegative.

A unitary matrix is normal. Its commuting Hermitian real and imaginary parts have orthogonal joint eigenspaces spanning the space, and an orthonormal basis subordinate to these spaces diagonalizes U. If P is the resulting unitary basis matrix, P adjoint times U times P is diagonal(z). Unitarity of this diagonal matrix gives |z(i)| = 1 for every i.

Conjugation by P tensor I turns the tensor sum into diagonal blocks with coefficients 1 + windowRoot(d)^y z(i). The scalar hypothesis bounds each coefficient sum. The diagonal block estimate applies, and unitary conjugation preserves operator norm. Consequently its action on a vector v has norm at most K times the norm of v; Cauchy-Schwarz also bounds the modulus of its pairing with w by K times the norms of w and v.

## References

- Truth anchor: `D5/S3/QuantumBounds/PeritoTensorBlockBound.norm_diagonal_tensor_sum_le`
- Truth anchor: `D5/S3/QuantumBounds/PeritoTensorBlockBound.tensor_block_bound`
- Dependency: [D5/S3/Observer/WindowRegister](../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/BlockNorm/EssentiallyHermitian](../Quantum/BlockNorm/EssentiallyHermitian.md)
