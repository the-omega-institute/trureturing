# Width-four scalar column Grams

## Abstract

Width-four scalar column Grams and the exact large-ratio thresholds.

**Definition 1.1 (Column Gram).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall lambda \in Real,\; (\operatorname{FourScalarGram}\left(a, b, c, d, lambda\right)) \Leftrightarrow (\exists X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \exists Y \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \operatorname{conjTranspose}\left(\sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right)\right) \cdot \sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), Complex\right))\right))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.FourScalarGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left matrices have a rows and b columns. The right matrices have d rows and c columns. The tensor sum acts from b times c input coordinates to a times d output coordinates. A positive scalar Gram makes this map a scaled isometry.

**Definition 1.2 (Dimension bounds for the constructions).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; (\operatorname{Staircase}\left(a, b, c, d\right)) \Leftrightarrow (((b \le a) \land (c \le d)) \lor (((a < b) \land ((3 \cdot b \le 4 \cdot a) \land (4 \cdot c \le 3 \cdot d))) \lor (((4 \cdot a < 3 \cdot b) \land ((2 \cdot b \le 3 \cdot a) \land (3 \cdot c \le 2 \cdot d))) \lor (((3 \cdot a < 2 \cdot b) \land ((3 \cdot b \le 5 \cdot a) \land (5 \cdot c \le 3 \cdot d))) \lor (((5 \cdot a < 3 \cdot b) \land ((b \le 2 \cdot a) \land (2 \cdot c \le d))) \lor (((2 \cdot a < b) \land ((2 \cdot b \le 5 \cdot a) \land (5 \cdot c \le 2 \cdot d))) \lor (((5 \cdot a < 2 \cdot b) \land ((b \le 3 \cdot a) \land (3 \cdot c \le d))) \lor ((3 \cdot a < b) \land ((b \le 4 \cdot a) \land (4 \cdot c \le d))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.Staircase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each upper bound on the left ratio includes equality. The inequalities use integer products, so they also specify the cases when a dimension vanishes.

**Theorem 1.3 (Sufficiency in both orientations).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow (((b = 0) \lor ((c = 0) \lor ((\operatorname{Staircase}\left(a, b, c, d\right)) \lor (\operatorname{Staircase}\left(d, c, b, a\right))))) \Rightarrow (\operatorname{FourScalarGram}\left(a, b, c, d, lambda\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.staircase_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coordinate rectangle contributes one Kronecker term. Its left and right maps carry the rectangle into its assigned output ranges. Disjoint images make the sum a coordinate isometry. Multiplying the left factors by the square root of lambda produces the specified column Gram.

At the four-thirds threshold the excess left inputs share the unused right coordinates across three parts of the right input. At the five-thirds threshold the right complement receives one rectangle spanning its full height and two rectangles with common left output and disjoint right output. At the five-halves threshold two full left blocks use separate right ranges. The two remaining rectangles use disjoint left ranges in the right complement.

Exchanging the factors permutes the pairs of input and output coordinates. The input permutation preserves the scalar identity.

**Theorem 1.4 (Minimum width at the first corner).**

$$\forall lambda \in Real,\; (0 < lambda) \Rightarrow ((\operatorname{FourScalarGram}\left(3, 4, 3, 4, lambda\right)) \land (\neg(\exists X \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(4\right), Complex\right),\; \exists Y \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(3\right), Complex\right),\; \operatorname{conjTranspose}\left(\sum_{i:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right)\right) \cdot \sum_{i:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(3\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(3\right)\right), Complex\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.exact_width_four_at_three_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four-thirds construction gives the column Gram. The width-three rectangular bound requires three times the right input dimension to be at most twice the right output dimension. The dimensions three and four violate that bound.

**Theorem 1.5 (Pure rank-two kernel bound).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \forall Y \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; (a < b) \Rightarrow ((\operatorname{LinearIndependent}\left(Complex, X\right)) \Rightarrow ((\operatorname{conjTranspose}\left(\sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right)\right) \cdot \sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right) = 1) \Rightarrow ((\sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{conjTranspose}\left(X\left(i\right)\right) \cdot X\left(i\right) = 1) \Rightarrow ((\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \Rightarrow ((\operatorname{compression}\left(X, T\right) = 0) \Rightarrow ((T \ne 0) \Rightarrow (\operatorname{rank}\left(T\right) = 2)))) \Rightarrow (4 \cdot c \le 3 \cdot d)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.pure_rank_two_kernel_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the left factor shrinks, a common kernel direction separates one isometric right range. The remaining three factors act on the kernel of the isolated left factor, which has positive dimension. Their right stack is injective and gives c ≤ 3(d − c). A neutral three-dimensional coefficient subspace instead gives three orthogonal isometric right ranges.

**Theorem 1.6 (Exact thresholds above twice the left output).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow ((0 < c) \Rightarrow ((2 \cdot a < b) \Rightarrow ((\operatorname{FourScalarGram}\left(a, b, c, d, lambda\right)) \Leftrightarrow (((2 \cdot a < b) \land ((2 \cdot b \le 5 \cdot a) \land (5 \cdot c \le 2 \cdot d))) \lor (((5 \cdot a < 2 \cdot b) \land ((b \le 3 \cdot a) \land (3 \cdot c \le d))) \lor ((3 \cdot a < b) \land ((b \le 4 \cdot a) \land (4 \cdot c \le d))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.native_four_scalar_gram_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive eigenspace of dimension at least two would give a subspace of codimension at most twice the left output dimension. Such a subspace meets the image of the left stack, contradicting zero compression. The same argument applied to the negative eigenspace leaves Hermitian rank at most two.

The common kernel case gives a residual width-three sum with left input dimension at least b − a and right output dimension d − c. The two width-three rectangular estimates give the first two thresholds. Above three times the left output dimension the coefficient kernel vanishes, and the four right ranges fit precisely when four times c is at most d.

**Theorem 1.7 (Exact thresholds above twice the right output).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow ((0 < b) \Rightarrow ((2 \cdot d < c) \Rightarrow ((\operatorname{FourScalarGram}\left(a, b, c, d, lambda\right)) \Leftrightarrow (((2 \cdot d < c) \land ((2 \cdot c \le 5 \cdot d) \land (5 \cdot b \le 2 \cdot a))) \lor (((5 \cdot d < 2 \cdot c) \land ((c \le 3 \cdot d) \land (3 \cdot b \le a))) \lor ((3 \cdot d < c) \land ((c \le 4 \cdot d) \land (4 \cdot b \le a))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.native_four_scalar_gram_swap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate permutations for the exchange of factors preserve the Gram identity and give the right-hand version of each threshold.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.FourScalarGram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.Staircase`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.exact_width_four_at_three_four`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.native_four_scalar_gram_iff`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.native_four_scalar_gram_swap_iff`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.pure_rank_two_kernel_bound`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase.staircase_sufficient`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourKernel](NativeFourKernel.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound](NativeThreeRectangularBound.md)
