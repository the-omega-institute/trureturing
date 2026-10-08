# The obstruction to acquiring a binary phase singleton

## Abstract

Binary initial phase singletons require two complete blocks and paid arrival.

**Theorem 1.1 (Every correct endpoint tree has horizon at least max(2,ceil(j/m))).**

$$\forall Y \in Type, k \in \mathbb{N}, m \in \mathbb{N}, j \in \mathbb{N}, A \in Y, B \in Y, v \in \operatorname{ZMod}\left(2\right), a \in Bool,\; \left(2 \le k \land \left(2 \le m \land \left(m < k \land \left(1 \le j \land \left(j \le k \land A \ne B\right)\right)\right)\right)\right) \Rightarrow \operatorname{let} marker=(\lambda (phi:\operatorname{ZMod}\left(k + 1\right)), \operatorname{ite}\left(phi = 0, 1, 0\right)) \operatorname{in} (\left(\forall phi \in \operatorname{ZMod}\left(k + 1\right),\; \operatorname{coefficient}\left(k, phi\right) = marker\left(phi\right) + marker\left(phi + 1\right)\right) \land \left(\left(\forall i \in \mathbb{N}, t \in \mathbb{N},\; i \le k \Rightarrow \left(t \le k \Rightarrow marker\left(-\operatorname{cast}\left(i, \operatorname{ZMod}\left(k + 1\right)\right) + \operatorname{cast}\left(t, \operatorname{ZMod}\left(k + 1\right)\right)\right) = \operatorname{ite}\left(t = i, 1, 0\right)\right)\right) \land \left(\left(\forall bits \in \operatorname{List}\left(Bool\right),\; \operatorname{runWord}\left(\operatorname{bitUpdate}\left(k\right), bits, none\right) = none\right) \land \left(\forall n \in \mathbb{N}, tree \in \operatorname{AcquisitionTree}\left(k, m, a, Y, n\right),\; \left(\forall i \in \mathbb{N}, s \in \mathbb{N},\; i \le k \Rightarrow \left(s < k \Rightarrow \operatorname{result}\left(tree, \operatorname{some}\left((v,-\operatorname{cast}\left(i, \operatorname{ZMod}\left(k + 1\right)\right),s)\right)\right) = \operatorname{ite}\left(i = j, B, A\right)\right)\right) \Rightarrow \operatorname{max}\left(2, \operatorname{ceilDiv}\left(j, m\right)\right) \le n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower.singleton_tree_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Y, distinct labels A and B, value v in ZMod(2), either alphabet, k>=2, 2<=m<k and 1<=j<=k, every tree that labels all initial records (v,-i,s) with i<=k and s<k by B exactly when i=j has horizon n>=max(2,ceil(j/m)). No coprimality assumption or separate survival premise is needed.

The marker is the indicator of zero phase with values in ZMod(2). Its adjacent sum is the literal coefficient; at phase -i+t for i,t<=k it is the indicator of t=i. Rejection is absorbing for every Boolean word. The casts in the formula take values in ZMod(k+1), and all marker arithmetic takes values in ZMod(2).

The literal transitions are those of `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel` and the trees have the endpoint semantics of `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells`. A first bit equal to one would reject every record with tail k-1, so a correct tree starts with zero. Before arrival at j, the zero and target phases have identical observations and archives, forcing the arrival bound. A one-block singleton would have total increment one, whereas adjacent marker cancellation makes that total zero. This forces two blocks.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower.singleton_tree_obstruction`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost](OriginalNarrowCost.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells](EndpointCells.md)
- Narrative reference: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel](LiteralModel.md)
