# Arbitrary Native J2 Frame Identification

## Abstract

Actual label relabelling earns arbitrary two-selected-label frame domains and all literal J2 ports without changing barred indices.

**Definition 1.1 (Actual Left Label Relabelling).**

$$\mathrm{relabel}\left(F\right) = \mathrm{Multiply}\left(\mathrm{anchor}\left(F\right), \mathrm{Inverse}\left(\mathrm{NativeRightPort}\left(m, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho is anchor(F) times the inverse of the independently specified native R0. It acts by left multiplication on configurations, so every native position generator remains the same.

**Definition 1.2 (Reverse Only the Two Selected Labels).**

$$\mathrm{reverseSelected}\left(F\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.reverseSelected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reversed frame uses selected.reverse with exactly the original base and terminal. Its full nodup and complete-label obligations are earned from the original frame. This operation does not reverse the base or rename indices one and two.

**Definition 1.3 (Actual Native Graph Isomorphism).**

$$\mathrm{frameDomainIso}\left(m, F\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.frameDomainIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For m at least five, left multiplication by rho is a graph isomorphism from the complete fixed F2 native domain to Layer(selected.toFinset, terminal :: base). Its vertex bijection follows from the earned full layer identification; its adjacency equivalence is the existing Cayley left-translation theorem.

**Theorem 1.4 (Every Actual Vertex Has the Independent Frame Domain).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall F \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Layer}\left(\mathrm{ToFinset}\left(\mathrm{Selected}\left(F\right)\right), \mathrm{CycleOfList}\left(\mathrm{Cons}\left(\mathrm{Terminal}\left(F\right), \mathrm{Base}\left(F\right)\right)\right), \mathrm{Multiply}\left(\mathrm{relabel}\left(F\right), x\right)\right) \Leftrightarrow \mathrm{F2Domain}\left(m, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_domain_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every SupplyFrame(m,2), a configuration rho*x lies in Layer(selected.toFinset, terminal :: base) exactly when x belongs to the independent F2Domain. The conclusion concerns every actual configuration, not only suppliers, ports, or one candidate walk. The proof transports deletion through an injective label map, identifies the erased actual anchor, and reuses the complete F2 layer theorem. No domain equivalence is a premise.

**Theorem 1.5 (All Original Unbarred Indices Are Preserved).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall F \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall i \in \mathrm{Fin}\left(3\right),\; \mathrm{Multiply}\left(\mathrm{relabel}\left(F\right), \mathrm{NativeRightPort}\left(m, i\right)\right) = \mathrm{rightPort}\left(F, \mathrm{FinValue}\left(i\right)\right) \land \mathrm{Multiply}\left(\mathrm{relabel}\left(F\right), \mathrm{NativeLeftPort}\left(m, i\right)\right) = \mathrm{leftPort}\left(F, \mathrm{FinValue}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_ports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same rho takes each original native R_i and L_i, for i in Fin(3), to the literal rightPort(F,i) and leftPort(F,i). The proof earns R_i = R0*(bc)^i from actual permutation values, then cancels the original anchor inverse. No endpoint correspondence is supplied as a premise.

**Theorem 1.6 (Barred Ports Use the Reversed Selected Frame at the Same Index).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall F \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall i \in \mathrm{Fin}\left(3\right),\; \mathrm{Multiply}\left(\mathrm{relabel}\left(F\right), \mathrm{NativeBar}\left(\mathrm{NativeRightPort}\left(m, i\right)\right)\right) = \mathrm{rightPort}\left(\mathrm{reverseSelected}\left(F\right), \mathrm{FinValue}\left(i\right)\right) \land \mathrm{Multiply}\left(\mathrm{relabel}\left(F\right), \mathrm{NativeBar}\left(\mathrm{NativeLeftPort}\left(m, i\right)\right)\right) = \mathrm{leftPort}\left(\mathrm{reverseSelected}\left(F\right), \mathrm{FinValue}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_barred_ports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same rho takes bar R_i and bar L_i to rightPort(reverseSelected(F),i) and leftPort(reverseSelected(F),i), at the original index i. The label transposition acts only on the two selected labels because the full tuple is nodup. Thus a later actual half-restoration consumer keeps the literal barred exception R0 to R1, L1 to R2 and L2 to L0. This identification does not supply a prior-cycle edge inventory or prove the all-size recursive Hamilton-cycle conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.frameDomainIso`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_barred_ports`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_domain_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.native_j2_frame_ports`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.relabel`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport.reverseSelected`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts](NativeJ2MarkedPorts.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply](NativeRecursiveSupply.md)
