# Native Full Source Production

## Abstract

One source-blind native stack program acquires and returns every finite source, retaining its full chronology and exact original node preorder.

**Definition 1.1 (Pending work and acquired subtrees).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Frame`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Frame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left frame stores a pending right-child address. A right frame stores the left subtree already constructed from actual replies. Frames contain no unknown input subtree.

**Definition 1.2 (Unbounded source-free workspace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Control`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Visit carries a literal address and a stack. Deliver carries an acquired subtree and its continuation stack. This carrier permits arbitrarily large finite stacks and acquired trees; the finite instruction description supplies no uniform finite carrier.

**Definition 1.3 (A fixed native instruction function).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.sourceControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.sourceControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Visit performs one NativeSerialMachine read. A leaf reply constructs its labelled leaf; a branch reply schedules the left child and saves the right address. Deliver switches to the pending right child or combines two acquired children using actual localStep instructions. An empty stack stops with the full acquired tree. The absent-reply branch makes the instruction function total; the proved runs never use it. Only local control is an argument: the unknown register, size, height, epoch, fuel and future tasks are absent.

**Definition 1.4 (The common initial control).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.initialControl`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.initialControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every input starts at Visit of the empty root address with an empty stack. It does not depend on the input source.

**Definition 1.5 (The complete native chronology).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.productionTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.productionTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The trace records a root read, then the left subtree, one local switch, the right subtree, and one local combination. A leaf contributes its single true read. Every event occurs at epoch zero and no update is issued. This tree-indexed trace describes the proved execution; it is not a runtime input or a stopping oracle.

**Theorem 1.6 (Exact sourcewise native termination).**

$$\forall U: Source, ((\operatorname{Run}\left(delta, initial, 0, U, \operatorname{T}\left(U\right), U\right)) \land (\forall old: Trace, (\exists c: Control, ((\operatorname{Reaches}\left(\operatorname{nativeStep}\left(delta\right), \operatorname{tuple}\left(initial, 0, U, old\right), \operatorname{tuple}\left(c, 0, U, \operatorname{append}\left(old, \operatorname{T}\left(U\right)\right)\right)\right)) \land (\operatorname{delta}\left(c\right) = \operatorname{stop}\left(U\right))))) \land (\forall old: Trace, (\forall x: \operatorname{Config}\left(Control\right), ((\operatorname{Reaches}\left(\operatorname{nativeStep}\left(delta\right), \operatorname{tuple}\left(initial, 0, U, old\right), x\right)) \implies ((\operatorname{epoch}\left(x\right) = 0) \land (\operatorname{register}\left(x\right) = U))))) \land (\operatorname{R}\left(U\right) = \operatorname{tagged}\left(\operatorname{H}\left(U\right)\right)) \land (\operatorname{A}\left(U\right) = \operatorname{nodes}\left(U\right)) \land (\operatorname{Nodup}\left(\operatorname{A}\left(U\right)\right)) \land (\operatorname{length}\left(\operatorname{R}\left(U\right)\right) = \operatorname{length}\left(\operatorname{nodes}\left(U\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.native_source_producer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Source, the same program terminates with that entire Source as output. Its nativeStep execution appends the complete productionTrace to any prior log, and every reachable configuration retains epoch zero and the initialized register. Retaining the read events and discarding the local-step markers yields exactly the existing acquisitionTrace with epoch-zero tags, in the original order and with the original replies. Its address list is exactly nodes, without duplicates, and its raw-call count is nodes.length. The proof's continuation invariant reconstructs a subtree into an arbitrary existing stack using actual read and localStep constructors. The preorder identity and absence of repeated nodes use ActualPureAcquisitionCompiler.trace_addresses and nodes_nodup. In the formula delta denotes sourceControl, initial denotes initialControl, T(U) denotes productionTrace [] U, H(U) denotes acquisitionTrace [] U, tagged tags each history entry with epoch zero, R(U) denotes reads(T(U)), A(U) maps each read to its address, epoch and register are configuration projections, tuple is the product constructor, append is list append, and Reaches is StateTransition.Reaches.

Termination is pointwise over all finite inputs, with workspace and trace length allowed to grow with the replies actually acquired. It supplies no uniform raw-call bound. NativeSerialDepth.bounded_serial_original_depth and the criterion_failure_arbitrary_depth obstruction distinguish a uniformly bounded whole-row contract from this pointwise producer. The present construction has no Partrec certification, OriginalEffectiveService inclusion, later-task handoff, physical-fee bound or continuous complete-law realization. Those conclusions require their own interfaces.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Control`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.Frame`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.initialControl`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.native_source_producer`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.productionTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.sourceControl`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler](ActualPureAcquisitionCompiler.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine](NativeSerialMachine.md)
