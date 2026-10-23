# Actual J2 Marked Edges in One F2 Hamilton Witness

## Abstract

All twelve independently defined J2 ports are actual F2 vertices, and one actual F2 Hamilton witness contains all six marked b edges while retaining its exact full edge inventory.

**Definition 1.1 (The Six Actual Native Circle Owners).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\mathrm{rightOwner}\left(m, \mathrm{Pair}\left(0, \mathrm{BoolFalse}\right)\right) = 1 \land \left(\mathrm{rightOwner}\left(m, \mathrm{Pair}\left(0, \mathrm{BoolTrue}\right)\right) = \mathrm{Swap}\left(0, m\right) \land \left(\mathrm{rightOwner}\left(m, \mathrm{Pair}\left(1, \mathrm{BoolFalse}\right)\right) = \mathrm{contactAnchor}\left(\mathrm{sub}\left(m, 3\right)\right) \land \left(\mathrm{rightOwner}\left(m, \mathrm{Pair}\left(1, \mathrm{BoolTrue}\right)\right) = \mathrm{lowerPort}\left(\mathrm{sub}\left(m, 3\right)\right) \land \left(\mathrm{rightOwner}\left(m, \mathrm{Pair}\left(2, \mathrm{BoolFalse}\right)\right) = \mathrm{gapAnchor}\left(\mathrm{contactAnchor}\left(\mathrm{sub}\left(m, 3\right)\right), \mathrm{sub}\left(m, 1\right)\right) \land \mathrm{rightOwner}\left(m, \mathrm{Pair}\left(2, \mathrm{BoolTrue}\right)\right) = \mathrm{gapAnchor}\left(\mathrm{contactAnchor}\left(\mathrm{sub}\left(m, 3\right)\right), \mathrm{sub}\left(m, 2\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.rightOwner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let j=m-3 and let tau exchange labels zero and m. The six independently specified right-port owners are identity, tau, contactAnchor(j), lowerPort(j), gapAnchor(contactAnchor(j),m-1), and gapAnchor(contactAnchor(j),m-2), indexed by the three port numbers and their label-swap bits. The actual surviving circle rows consume these exact owners.

**Theorem 1.2 (Every Actual Port Has Its Specified Native Owner).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Prod}\left(\mathrm{Bool}, \mathrm{Bool}\right)\right),\; \mathrm{Circle}\left(\mathrm{rightOwner}\left(m, \mathrm{CutIndexOf}\left(p\right)\right), \mathrm{port}\left(m, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_port_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, each actual port lies in the native circle anchored by rightOwner at the same right-port number and label-swap bit. The six right-port rotation identities establish this for the right endpoints. Multiplication by b stays in the same independently specified native circle, giving the left endpoints. Port-domain membership and exclusion of marked edges from intermediate complete native-circle complements consume this owner fact.

**Theorem 1.3 (Every Actual J2 Port Belongs to F2).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Prod}\left(\mathrm{Bool}, \mathrm{Bool}\right)\right),\; \mathrm{F2Domain}\left(m, \mathrm{port}\left(m, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_port_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and p in Fin(3) times Bool times Bool, port(m,p) lies in the independently specified F2Domain. Let j=m-3, rho=finRotate(m+1), and T exchange the actual labels 0 and m. The six right ports have the precise native-owner identities R0=rho^m, bar(R0)=T*rho^m, R1=contactAnchor(j)*rho^m, bar(R1)=lowerPort(j)*rho, R2=gapAnchor(contactAnchor(j),m-1)*rho, and bar(R2)=gapAnchor(contactAnchor(j),m-2)*rho^2. The first two belong to the two normalized core-cut circles, the fourth to a lower T circle, and the remaining ones to actual contact-supplier gap circles. Actual rotations preserve each full native circle. Each left port is the corresponding right port multiplied by b, so the earned native-edge endpoint law places it in the same owner circle. The proof uses the earned complete core and supplier partitions, rather than assuming port membership.

**Theorem 1.4 (All Six Actual Marked Edges Avoid the Full T/E Cut Set).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; \neg \mathrm{F2DeletedEdge}\left(m, \mathrm{markedEdge}\left(m, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_marked_uncut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and p in Fin(3) times Bool, markedEdge(m,p) does not belong to F2DeletedEdge. The marked-edge identity makes it the actual b edge at its right port. Every actual port has terminal value m-1, while the complete b-cut classification permits only terminal 0 in a lower T circle or contact supplier and terminal m in an upper T circle. Since m-1 differs from both, every marked edge is uncut. This is a consumed application of the existing terminal and complete cut classification.

**Theorem 1.5 (One and the Same Hamilton Cycle Contains Every Marked Edge).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\exists base \in \mathrm{Vertices}\left(\mathrm{F2Domain}\left(m\right)\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{domainGraph}\left(\mathrm{F2Domain}\left(m\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\forall e \in \mathrm{Sym2}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{Member}\left(e, \mathrm{RawEdges}\left(w\right)\right) \Leftrightarrow \left(\left(\mathrm{F2NativeEdge}\left(m, e\right) \land \left(\neg \mathrm{F2DeletedEdge}\left(m, e\right)\right)\right) \lor \mathrm{F2Seam}\left(m, e\right)\right)\right) \land \left(\left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Prod}\left(\mathrm{Bool}, \mathrm{Bool}\right)\right),\; \mathrm{F2Domain}\left(m, \mathrm{port}\left(m, p\right)\right)\right) \land \left(\forall p \in \mathrm{Prod}\left(\mathrm{Fin}\left(3\right), \mathrm{Bool}\right),\; \mathrm{Member}\left(\mathrm{markedEdge}\left(m, p\right), \mathrm{RawEdges}\left(w\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_hamiltonian_cycle_with_marked_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, there is one actual Hamilton cycle w on F2Domain with all three facts simultaneously: its raw undirected edges have the exact full closed F2 inventory; all twelve actual J2 ports lie in its vertex domain; and all six marked edges occur in its raw edge list. The witness is obtained once from the earned native-edge inventory theorem. Its actual native-edge retention criterion then applies to each marked right port using the proved domain membership and the proved exclusion from the full cut set. The closed inventory is retained unchanged for that same witness: an arbitrary raw edge occurs exactly when it is a native F2 edge outside F2DeletedEdge or an actual F2Seam.

The independently proved twelve-port injection gives the six marked cuts disjoint endpoints. This layer places those cuts in one specific certified F2 Hamilton witness. Legality of the five literal J2 words after the six cuts, their nonbacktracking paths, exhaustion of path components, and all-size Hamiltonicity remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_hamiltonian_cycle_with_marked_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_marked_uncut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_port_circle`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.native_j2_port_domain`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.rightOwner`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts](NativeJ2MarkedPorts.md)
