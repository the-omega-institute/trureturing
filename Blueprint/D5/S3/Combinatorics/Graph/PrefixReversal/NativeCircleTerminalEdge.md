# Unique Native b Edge at a Fixed Last Label

## Abstract

A fixed last label determines exactly one undirected b edge in an actual complete native circle.

**Theorem 1.1 (Exactly Two Circle Orientations Have the Anchor's Last Label).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Circle}\left(z, x\right) \Rightarrow \left(\mathrm{LastLabel}\left(m, x\right) = \mathrm{LastLabel}\left(m, z\right) \Leftrightarrow \left(x = z \lor x = \mathrm{Mul}\left(z, \mathrm{b}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge.native_circle_same_last_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least three, every actual anchor z and every configuration x in its complete rotation/reversal circle, x and z have the same last label exactly when x=z or x=zb. The actual circle equivalence supplies rotation/reflection coordinates. In positive orientation the equal last label forces rotation zero. In negative orientation it forces the last rotation index, which is minus one; the existing actual identity b=finCycle(-1)*a identifies the second orientation.

**Theorem 1.2 (All Such Orientations Give the Same Undirected b Edge).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Circle}\left(z, x\right) \land \mathrm{LastLabel}\left(m, x\right) = \mathrm{LastLabel}\left(m, z\right)\right) \Rightarrow \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, \mathrm{b}\left(m\right)\right)\right) = \mathrm{Sym2Pair}\left(z, \mathrm{Mul}\left(z, \mathrm{b}\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge.native_circle_terminal_b_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If x belongs to the actual circle of z and has z's last label, the undirected b edge from x to xb is exactly the edge from z to zb. The preceding orientation classification gives x=z or x=zb; b squared is the identity, so the second case only exchanges the two endpoints. The result is independent of any chosen complement path or Hamilton cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge.native_circle_same_last_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge.native_circle_terminal_b_edge`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement](NativeCircleComplement.md)
