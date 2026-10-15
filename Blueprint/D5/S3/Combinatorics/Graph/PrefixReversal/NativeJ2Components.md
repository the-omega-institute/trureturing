# The Complete Actual J2 Component Partition

## Abstract

Six actual complete path components partition the full independently defined F2 domain.

**Definition 1.1 (The Six Independently Specified Starting Ports).**

$$\forall i \in \mathrm{Fin}\left(6\right),\; \mathrm{componentStartPort}\left(i\right) = \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(0, \mathrm{False}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(0, \mathrm{False}, \mathrm{True}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 2, \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 3, \mathrm{Tuple3}\left(2, \mathrm{False}, \mathrm{True}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 4, \mathrm{Tuple3}\left(0, \mathrm{True}, \mathrm{False}\right), \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{True}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.componentStartPort` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In index order zero through five, the starts are R0, L0, R1, L2, bar R0, and L1.

**Definition 1.2 (The Six Independently Specified Finishing Ports).**

$$\forall i \in \mathrm{Fin}\left(6\right),\; \mathrm{componentFinishPort}\left(i\right) = \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 0, \mathrm{Tuple3}\left(2, \mathrm{False}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 1, \mathrm{Tuple3}\left(1, \mathrm{True}, \mathrm{True}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 2, \mathrm{Tuple3}\left(2, \mathrm{True}, \mathrm{True}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 3, \mathrm{Tuple3}\left(2, \mathrm{True}, \mathrm{False}\right), \mathrm{IfThenElse}\left(\mathrm{FinValue}\left(i\right) = 4, \mathrm{Tuple3}\left(1, \mathrm{True}, \mathrm{False}\right), \mathrm{Tuple3}\left(0, \mathrm{True}, \mathrm{True}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.componentFinishPort` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the same order, the finishes are R2, bar L1, bar L2, bar R2, bar R1, and bar L0.

**Theorem 1.3 (Every Actual F2 Vertex Lies in Exactly One of Six Components).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\exists paths \in \mathrm{DependentWalkFamily}\left(\mathrm{Fin}\left(6\right), \mathrm{survivingGraph}\left(m\right), \mathrm{componentStartPort}, \mathrm{componentFinishPort}, m\right),\; \left(\forall i \in \mathrm{Fin}\left(6\right),\; \mathrm{IsPath}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \land \left(\left(\forall i \in \mathrm{Fin}\left(6\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \Leftrightarrow \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{port}\left(m, \mathrm{componentStartPort}\left(i\right)\right), x\right)\right) \land \left(\left(\forall i \in \mathrm{Fin}\left(6\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Adj}\left(\mathrm{survivingGraph}\left(m\right), x, y\right) \land \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{port}\left(m, \mathrm{componentStartPort}\left(i\right)\right), x\right)\right) \Leftrightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(\mathrm{apply}\left(paths, i\right)\right)\right)\right) \land \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2Domain}\left(m, x\right) \Leftrightarrow \left(\exists i \in \mathrm{Fin}\left(6\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, i\right)\right)\right) \land \left(\forall j \in \mathrm{Fin}\left(6\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(\mathrm{apply}\left(paths, j\right)\right)\right) \Rightarrow j = i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.native_j2_six_component_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, there is a dependent family of six actual surviving walks with independently specified starts and finishes. Every walk is a simple path and exhausts exactly its reachable component, including every actual edge incident to that component. A configuration lies in F2Domain(m) exactly when it belongs to the support of a unique member of this family.

The endpoint table, in index order zero through five, is R0 to R2, L0 to bar L1, R1 to bar L2, L2 to bar R2, bar R0 to bar R1, and L1 to bar L0. These ports are defined independently of every path. The first five actual walks come from the complete literal words, and the sixth comes from the actual remaining six-cut slice. Every slice has a marked port at its start; the complete twelve-port endpoint table connects that slice to one of the six stated paths. Full component support then earns domain coverage. If a vertex belonged to two supports, reachability would put one independent starting port inside the other simple path. Its graph-leaf property forces it to be one of that path's endpoints. Actual port injectivity and the independent endpoint table force the two indices to be equal.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.componentFinishPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.componentStartPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components.native_j2_six_component_partition`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent](NativeJ2SixthComponent.md)
