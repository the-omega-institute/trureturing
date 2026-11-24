# Rank-three coefficient kernels at width four

## Abstract

Right dimension bounds from a rank-three Hermitian coefficient.

**Theorem 1.1 (Dimension bounds from a rank-three compression kernel member).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; \forall X \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \forall Y \in \operatorname{Fin}\left(4\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \forall lambda \in Real,\; (0 < lambda) \Rightarrow ((a < b) \Rightarrow ((\operatorname{conjTranspose}\left(\sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right)\right) \cdot \sum_{i:\operatorname{Fin}\left(4\right)} \operatorname{kronecker}\left(X\left(i\right), Y\left(i\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), Complex\right))\right)) \Rightarrow ((\exists T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), Complex\right),\; (\operatorname{IsHermitian}\left(T\right)) \land ((\operatorname{compression}\left(X, T\right) = 0) \land (\operatorname{rank}\left(T\right) = 3))) \Rightarrow ((6 \cdot c \le 5 \cdot d) \land ((a \cdot d - b \cdot c < 2 \cdot c - d) \Rightarrow (4 \cdot c \le 3 \cdot d))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourRankThree.rank_three_small_defect_four_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rank-three Hermitian coefficient yields an isometric right combination and an orthogonal combination of rank at most the difference of the right dimensions. On the kernel of the latter, the tensor has width at most three.

When the right dimensions violate the stronger bound, the isolated isometry on that kernel determines the right output slice. The small row defect forces the paired left factor to be a coisometry. Projecting to the perpendicular right output then bounds its rank by the three remaining factors and the row defect.

At (4,5,4,5), (5,6,4,5), and (5,6,5,6), the row defects are zero, one, and zero. They are smaller than the corresponding thresholds three, three, and four. At each size the stronger dimension inequality forbids a rank-three coefficient.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourRankThree.rank_three_small_defect_four_bound`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourCliffordRankThree](NativeFourCliffordRankThree.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeFourStaircase](NativeFourStaircase.md)
