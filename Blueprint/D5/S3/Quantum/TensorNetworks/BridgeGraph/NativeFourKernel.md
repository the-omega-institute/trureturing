# Hermitian compression at width four

## Abstract

Spectral dimension bounds and rank-two coefficient spaces for a stack of four matrices.

**Definition 1.1 (Compression to the left stack).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; \operatorname{compression}\left(X, T\right) = \operatorname{conjTranspose}\left(\operatorname{stackK}\left(X\right)\right) \cdot \operatorname{kronecker}\left(T, (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(a\right), Complex\right))\right) \cdot \operatorname{stackK}\left(X\right)$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.compression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stacking the four left factors identifies the coefficient form on their common input by applying the coefficient matrix to the four copies of the output.

**Theorem 1.2 (Adjoint).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; \operatorname{compression}\left(X, \operatorname{conjTranspose}\left(T\right)\right) = \operatorname{conjTranspose}\left(\operatorname{compression}\left(X, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.compression_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the adjoint reverses the two multiplications by the stack.

**Theorem 1.3 (Eigenvalue multiplicities).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; (\operatorname{Injective}\left(\operatorname{mulVecLin}\left(\operatorname{stackK}\left(X\right)\right)\right)) \Rightarrow (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (\forall k \in Nat,\; (k \le 3) \Rightarrow ((k \cdot a < b) \Rightarrow (\operatorname{rank}\left(T\right) < 2 \cdot \left(4 - k\right) - 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.hermitian_rank_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection to the nonpositive directions of a diagonalized coefficient form is injective on the range of the left stack. A vector killed by the projection would have strictly positive energy unless it vanished. Negating the coefficient form gives the other sign bound, and the two multiplicities sum to its rank.

**Theorem 1.4 (Rank-two alternatives).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; (\operatorname{LinearIndependent}\left(Complex, X\right)) \Rightarrow ((\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (\operatorname{rank}\left(T\right) \le 2))) \Rightarrow ((\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (T = 0))) \lor ((\exists v \in \operatorname{Fin}\left(4\right) \to Complex,\; (v \ne 0) \land (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (\operatorname{mulVec}\left(T, v\right) = 0)))) \lor (\exists E \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(3\right), Complex\right),\; (\operatorname{rank}\left(E\right) = 3) \land (\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow (\operatorname{conjTranspose}\left(E\right) \cdot T \cdot E = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.coefficient_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero form of rank at most two has both signs. After congruence it has diagonal entries one, minus one, zero, zero. The three-by-three minors at the sum and difference of the diagonal form and an arbitrary Hermitian member give a zero lower block and equal outer products of the two upper rows of the off-diagonal block.

If the first rows are proportional across the space, a common vector in the last two coordinates is killed by every member. If two first rows are independent, the rank-one condition on their sum forces the same row ratio throughout. The three-by-three minors then give a third neutral direction orthogonal to the common image of the off-diagonal blocks.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.coefficient_geometry`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.compression`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.compression_star`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel.hermitian_rank_bound`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound](NativeRectangularBound.md)
