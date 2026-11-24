# Clifford coefficient kernels at width four

## Abstract

Right dimension bound from the Pauli Clifford coefficient kernel.

**Definition 1.1 (Pauli Clifford matrices).**

$$(\operatorname{pauliClifford}\left(0\right) = \begin{pmatrix}0&0&1&0\\0&0&0&1\\1&0&0&0\\0&1&0&0\end{pmatrix}) \land ((\operatorname{pauliClifford}\left(1\right) = \begin{pmatrix}0&0&-\mathrm{i}&0\\0&0&0&-\mathrm{i}\\\mathrm{i}&0&0&0\\0&\mathrm{i}&0&0\end{pmatrix}) \land ((\operatorname{pauliClifford}\left(2\right) = \begin{pmatrix}0&1&0&0\\1&0&0&0\\0&0&0&-1\\0&0&-1&0\end{pmatrix}) \land ((\operatorname{pauliClifford}\left(3\right) = \begin{pmatrix}0&-\mathrm{i}&0&0\\\mathrm{i}&0&0&0\\0&0&0&\mathrm{i}\\0&0&-\mathrm{i}&0\end{pmatrix}) \land (\operatorname{pauliClifford}\left(4\right) = \begin{pmatrix}1&0&0&0\\0&-1&0&0\\0&0&-1&0\\0&0&0&1\end{pmatrix}))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree.pauliClifford` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five matrices are written in tensor-product coordinates, with the first index ordered before the second. The Pauli matrices have off-diagonal entries one and one for sigma x, minus i and i for sigma y, and diagonal entries one and minus one for sigma z. Each unspecified entry is zero.

**Theorem 1.2 (Four-input to three-output dimension bound).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \forall Y \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow ((a < b) \Rightarrow ((\operatorname{conjTranspose}\left(\sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right)\right) \cdot \sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), Complex\right))\right)) \Rightarrow ((\exists P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsUnit}\left(P\right)) \land (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (\operatorname{conjTranspose}\left(P\right) \cdot T \cdot P \in \operatorname{span}\left(Real, \operatorname{range}\left(pauliClifford\right)\right))))) \Rightarrow (4 \cdot c \le 3 \cdot d))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree.clifford_kernel_four_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient matrices of the right Gram differ from their normalized trace by elements of the compression kernel. After congruence these differences have two scalar diagonal blocks with opposite signs and two linked off-diagonal blocks.

Diagonalizing the scalar trace on each pair makes the right factors within each pair orthogonal. A strict diagonal gap makes one factor injective. When the two gaps vanish, the cross blocks kill the common kernel of the first pair, so the second pair supplies two orthogonal injective extensions.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree.clifford_kernel_four_bound`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree.pauliClifford`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel](NativeFourKernel.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound](NativeThreeRectangularBound.md)
