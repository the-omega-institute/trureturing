# Physical Direction Tapes and Paid Terminal Tests

## Abstract

Complete direction functions determine finite ordered terminal frontiers.

Source is FreeMagma Bool, the existing finite nonempty ordered full binary tree. Its leaf labels are alpha (true) and beta (false). An Address is a finite Boolean list: false is physical a, true is physical b, and concatenation is written append. readout has the existing four values alpha, beta, branch and absent. Only absence versus presence is used by the walks. Height is the height of the existing ordered shape decompose(T).1, so a leaf has height zero.

**Definition 1.1 (Direction depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.depth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf returns zero for every tape. At a branch a leading false chooses the left child and a leading true chooses the right child; the result is one plus the child's depth on the tail. The total definition returns zero at an exhausted branch. Every walk asserted below has enough remaining directions to reach a leaf, and therefore never uses that extra case.

**Definition 1.2 (Full root query operands).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.probes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.probes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the current physical address p the first operand is append(p,[false]), including at a terminal node with an empty tape. After choosing b the next current address is append(p,[b]). The list retains every query operand, in chronological order, including the final absent-child test.

**Definition 1.3 (Paid presence walk).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.PaidWalk`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.PaidWalk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PaidWalk(U,p,u,tr,d) is the finite serial derivation in the same full root U. A stop requires readout(append(p,[false]),U)=absent and records that operand. A step requires its presence, consumes one direction b, continues at append(p,[b]), and increments the edge count. Exhaustion alone is not a stop rule. This is a mathematical description of the original stationary presence service; root binding, grants, backing and completed serial reads remain premises for using that service.

**Definition 1.4 (Finite-tape control).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.Control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.Control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A walk state contains only the current absolute address, remaining tape and accumulated edge count. A stop state contains the returned count.

**Definition 1.5 (Original serial Read controller).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.controller`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.controller` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every walk state first issues a native Read at append(p,[false]). Absence selects stop. Presence with a next direction b selects walk(append(p,[b]),tail,k+1). The total control also stops on exhausted presence, a case excluded by every asserted sufficient-horizon paid walk. A stop state executes the original stop operation; no source, descriptor or clock is an input to the control, and it issues no update.

**Definition 1.6 (Actual stationary Read trace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.eventTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.eventTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

eventTrace(e,U,qs) maps every operand a to the native event Read(e,a,readout(a,U)). Run is the existing NativeSerialMachine.Run: the same physical root is passed between reads, and every final absent reply remains an actual charged read event.

**Theorem 1.7 (Complete tape geometry).**

$$\forall T: Source, ((\forall U: Source, (\forall p: Address, (\forall u: Address, ((\forall w: Address, (\operatorname{readout}\left(\operatorname{append}\left(p, w\right), U\right) = \operatorname{readout}\left(w, T\right))) \implies ((\operatorname{height}\left(T\right) \leq \operatorname{length}\left(u\right)) \implies ((\operatorname{PaidWalk}\left(U, p, u, \operatorname{probes}\left(T, p, u\right), \operatorname{depth}\left(T, u\right)\right)) \land \\(\forall e: Nat, (\operatorname{Run}\left(controller, \operatorname{walk}\left(p, u, 0\right), e, U, \operatorname{eventTrace}\left(e, U, \operatorname{probes}\left(T, p, u\right)\right), \operatorname{depth}\left(T, u\right)\right))))))))) \land \\(\forall p: Address, (\forall u: Address, (\operatorname{length}\left(\operatorname{probes}\left(T, p, u\right)\right) = \operatorname{depth}\left(T, u\right) + 1))) \land \\(\forall u: Address, (\operatorname{depth}\left(T, u\right) \leq \operatorname{height}\left(T\right))) \land \\(\forall u: Address, (\forall v: Address, ((\operatorname{height}\left(T\right) \leq \operatorname{length}\left(u\right)) \implies (\operatorname{depth}\left(T, \operatorname{append}\left(u, v\right)\right) = \operatorname{depth}\left(T, u\right))))) \land \\(\forall L: Nat, ((\operatorname{height}\left(T\right) \leq L) \implies (\exists u: Address, ((\operatorname{length}\left(u\right) = L) \land \\(\operatorname{depth}\left(T, u\right) = \operatorname{height}\left(T\right)))))) \land \\(\forall U: Source, (\forall p: Address, ((\operatorname{subtree}\left(p, U\right) = \operatorname{some}\left(T\right)) \implies ((\operatorname{length}\left(p\right) + \operatorname{height}\left(T\right) \leq \operatorname{height}\left(U\right)) \land \\(\forall u: Address, (\operatorname{depth}\left(U, \operatorname{append}\left(p, u\right)\right) = \operatorname{length}\left(p\right) + \operatorname{depth}\left(T, u\right))))))) \land \\(\forall U: Source, (\forall L: Nat, ((\operatorname{height}\left(T\right) \leq L) \implies ((\operatorname{height}\left(U\right) \leq L) \implies ((\forall u: Address, ((\operatorname{length}\left(u\right) = L) \implies (\operatorname{depth}\left(T, u\right) = \operatorname{depth}\left(U, u\right)))) \implies (\operatorname{decompose}\left(T\right).1 = \operatorname{decompose}\left(U\right).1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.tape_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All tree, literal, tape and horizon quantifiers are unrestricted. The location hypothesis compares every suffix in the same full root, rather than supplying a second relative root. Induction on the finite tree proves the paid walk, the exact number depth+1 of reads, the all-tape height bound, and independence from every appended padding word. Choosing a child of maximum height recursively attains the bound at every sufficient horizon.

An existing subtree at p gives both its remaining height bound and the exact prefix offset for every suffix tape. Equal complete depth functions force matching terminal reports after erasing the leaf labels. The existing source_foundation complete-frontier rigidity theorem then identifies the ordered unlabelled shapes. No leaf-label recovery, future observation equivalence, source acquisition or resource bound follows.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.Control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.PaidWalk`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.controller`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.depth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.eventTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.probes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/PhysicalTapeDepth.tape_geometry`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](../Observer/NativeSerialMachine.md)
