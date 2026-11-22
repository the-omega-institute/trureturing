# Width-three scalar column Gram classification

## Abstract

Exact dimension criteria for a positive scalar column Gram of a width-three tensor sum.

**Definition 1.1 (Admissible dimensions).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; (\operatorname{ScalarGramAdmissible}\left(a, b, c, d\right)) \Leftrightarrow ((b = 0) \lor ((c = 0) \lor (((b \le a) \land (c \le d)) \lor (((a < b) \land (((2 \cdot b \le 3 \cdot a) \land (3 \cdot c \le 2 \cdot d)) \lor (((3 \cdot a < 2 \cdot b) \land ((b \le 2 \cdot a) \land (2 \cdot c \le d))) \lor ((2 \cdot a < b) \land ((b \le 3 \cdot a) \land (3 \cdot c \le d)))))) \lor ((d < c) \land (((2 \cdot c \le 3 \cdot d) \land (3 \cdot b \le 2 \cdot a)) \lor (((3 \cdot d < 2 \cdot c) \land ((c \le 2 \cdot d) \land (2 \cdot b \le a))) \lor ((2 \cdot d < c) \land ((c \le 3 \cdot d) \land (3 \cdot b \le a))))))))))$$

*Formalization.* `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification.ScalarGramAdmissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If either input dimension vanishes, the tensor input is empty. Otherwise, the dimensions are admissible when both factors fit into their respective output spaces or when one factor shrinks and the other meets the corresponding threshold. When the input is nonempty and either output dimension vanishes, every clause fails.

**Theorem 1.2 (Exact existence criterion).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow ((\exists M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \exists N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \operatorname{conjTranspose}\left(\sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)\right) \cdot \sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), Complex\right))\right)) \Leftrightarrow (\operatorname{ScalarGramAdmissible}\left(a, b, c, d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification.native_scalar_gram_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a shrinking left factor, the three rectangular bounds give the successive requirements on the right output dimension. The Gram has full column rank, so the upper bound on the rank of a width-three tensor sum also gives b ≤ 3a when the right input dimension is positive.

For the one-, two- and three-block constructions, split the left inputs into blocks of size at most a. Each block embeds into the same left output coordinates and sends the right inputs to its own block of c output coordinates. The images of the input coordinates are therefore distinct. Scaling the left factors by the square root of lambda gives the prescribed Gram. At the first rectangular threshold, the excess left inputs use the even and odd routes determined by the two parts of the right input.

Exchanging the tensor factors permutes the output and input coordinates. The resulting column Gram is the original Gram reindexed by the input permutation, which preserves the scalar identity. This transports the construction and the dimension bounds when the right factor shrinks.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification.ScalarGramAdmissible`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGramClassification.native_scalar_gram_iff`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram](NativeScalarGram.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound](NativeThreeRectangularBound.md)
