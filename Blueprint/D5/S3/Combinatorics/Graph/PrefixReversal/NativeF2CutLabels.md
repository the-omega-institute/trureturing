# Literal F2 Cut Generators and Endpoint Labels

## Abstract

The complete unmarked F2 cut set has exactly two a edges and a complete geometric b-edge classification.

Configurations are actual permutations of Fin(m+1). The selected labels are p=0 and q=FinLast(m). MarkerSwap(m) is the actual transposition Equiv.swap(0,FinLast(m)). F2DeletedEdge is the already earned complete literal T/E cut set of the unmarked actual F2 cycle.

**Theorem 1.1 (Exactly Two Actual a Edges Are Cut).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2DeletedEdge}\left(m, \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, \mathrm{a}\left(m\right)\right)\right)\right) \Leftrightarrow \left(\mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, \mathrm{a}\left(m\right)\right)\right) = \mathrm{Sym2Pair}\left(\mathrm{One}, \mathrm{a}\left(m\right)\right) \lor \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, \mathrm{a}\left(m\right)\right)\right) = \mathrm{Sym2Pair}\left(\mathrm{MarkerSwap}\left(m\right), \mathrm{Mul}\left(\mathrm{MarkerSwap}\left(m\right), \mathrm{a}\left(m\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels.native_f2_a_cut_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four and every configuration x, the a edge from x to xa belongs to F2DeletedEdge exactly when it is the undirected edge from 1 to a or the edge from MarkerSwap to MarkerSwap*a. Actual generator uniqueness excludes every b cut. The T owner index has generator a precisely at its last two lower indices. The first cut start is 1; the second is normalized to MarkerSwap by the existing actual T half-word product theorem.

**Theorem 1.2 (The Three Exact Circle and Star Conditions for b Cuts).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{F2DeletedEdge}\left(m, \mathrm{Sym2Pair}\left(x, \mathrm{Mul}\left(x, \mathrm{b}\left(m\right)\right)\right)\right) \Leftrightarrow \left(\left(\exists j \in \mathrm{Fin}\left(\mathrm{NatSub}\left(m, 2\right)\right),\; \mathrm{Circle}\left(\mathrm{lowerPort}\left(j\right), x\right) \land \mathrm{LastLabel}\left(m, x\right) = 0\right) \lor \left(\left(\exists j \in \mathrm{Fin}\left(\mathrm{NatSub}\left(m, 2\right)\right),\; \mathrm{Circle}\left(\mathrm{upperPort}\left(j\right), x\right) \land \mathrm{LastLabel}\left(m, x\right) = \mathrm{FinLast}\left(m\right)\right) \lor \left(\exists j \in \mathrm{Fin}\left(\mathrm{NatSub}\left(m, 2\right)\right),\; \mathrm{SupplierStar}\left(\mathrm{contactAnchor}\left(j\right), x\right) \land \mathrm{LastLabel}\left(m, x\right) = 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels.native_f2_b_cut_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four and every actual configuration x, the b edge from x to xb belongs to the complete literal F2 cut set exactly when one of three independent geometric conditions holds. First, x lies in a lowerPort(j) native circle and its last label is zero. Second, x lies in an upperPort(j) native circle and its last label is FinLast(m). Third, x lies in the full remaining supplier star of contactAnchor(j) and its last label is zero. Each index j ranges over Fin(m-2). No F2 domain membership is assumed.

Forward classification uses actual undirected generator uniqueness to exclude the two lower a cuts. The other T cut starts normalize to their literal lower and upper ports. Supplier cuts range over every gap, including gap zero. Backward classification uses the uniqueness of the b edge at an anchor's last label in a complete native circle; the complete supplier circle partition then covers every configuration in the supplier-star case.

The later six v-marked cuts are additional cuts and are not part of this unmarked F2 classification.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels.native_f2_a_cut_classification`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2CutLabels.native_f2_b_cut_classification`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleTerminalEdge](NativeCircleTerminalEdge.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification](NativeF2EdgeClassification.md)
