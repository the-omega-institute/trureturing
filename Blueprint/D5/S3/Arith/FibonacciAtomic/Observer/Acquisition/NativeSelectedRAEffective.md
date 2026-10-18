# Effective native selected production

## Abstract

A single effective source independent machine with complete selected rows.

The complete configuration consists of entry, active finite control with unbounded finite address and byte regions, or the common ready configuration. The program takes no source, schedule, update count or size bound as input. Its only source access is the actual Read reply.

**Definition 1.1 (The whole finite configuration code).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodeState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodeState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An injective natural code retains every field of Work and both selected ready rows. Work is encoded as its finite control, two finite binary addresses, finite sixteen letter row and three finite reply latches. The state constructors use disjoint sum codes. This is a code of all accessible cells; no workspace field is projected away.

**Definition 1.2 (Finite data for each microstep).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.finiteInstruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.finiteInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each Read instruction carries its address and all four encoded continuation configurations. Every local instruction carries its whole encoded successor. Ready is a separate Return. The finite program counter is dispatched independently of the unbounded data regions. List append, retraction, last cell tests and constructor tests are primitive recursive.

**Definition 1.3 (The total numeric instruction function).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.numericInstruction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.numericInstruction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decode the complete natural control and execute finiteInstruction. Invalid natural codes use the same fixed entry configuration. This total function is primitive recursive.

**Definition 1.4 (Exact instruction correspondence).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodedOp`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodedOp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Encode just the complete control of a local step or each of the four Read continuations, preserving the actual address and instruction kind. Return stays Return.

**Theorem 1.5 (One recursive program realizes every microstep).**

$$(\operatorname{Injective}\left(\operatorname{encodeState}\right)) \land (\exists P: \operatorname{EffectiveProgram}, (\forall x: \operatorname{State}, (\operatorname{transition}\left(P, \operatorname{encodeState}\left(x\right)\right) = \operatorname{encodedOp}\left(\operatorname{step}\left(x\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.effective_selected_machine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one finite recursive code computing numericInstruction at every natural control, and its transition at every encoded actual configuration is exactly encodedOp of the original step. The primitive recursive construction covers all controls and data lengths, including configurations not reachable from entry. It identifies one actual program instruction at a time, preserving local steps and the separate Return. It makes no claim that the evaluator's own internal computation steps are physical observer instructions.

**Theorem 1.6 (Complete source independent selected production).**

$$((\operatorname{Injective}\left(\operatorname{encodeState}\right)) \land (\exists P: \operatorname{EffectiveProgram}, (\forall x: \operatorname{State}, (\operatorname{transition}\left(P, \operatorname{encodeState}\left(x\right)\right) = \operatorname{encodedOp}\left(\operatorname{step}\left(x\right)\right))))) \land (\forall u: \operatorname{Source}, (\forall h: \operatorname{Word}, (\forall b: \operatorname{State}, (\operatorname{Run}\left(\operatorname{step}, \operatorname{entry}, u, h, b\right) \implies \exists q: \operatorname{Bool}, (\exists r: \operatorname{List}\left(\operatorname{Cell}\right), ((b = \operatorname{ready}\left(q, r\right)) \land (\operatorname{Captured}\left(u, \operatorname{eventSchedule}\left(h\right), \operatorname{length}\left(h\right), q, r\right)))))))) \land (\forall u: \operatorname{Source}, (\forall s: \operatorname{Nat} \to \operatorname{Bool}, (\operatorname{Finite}\left(\{n:\operatorname{Nat} \Vert (\operatorname{apply}\left(s, n\right) = \operatorname{true}) \land (\operatorname{returned}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), n\right)\right) = \operatorname{false})\}\right) \implies \exists m: \operatorname{Nat}, (\operatorname{returned}\left(\operatorname{trajectory}\left(s, \operatorname{world}\left(\operatorname{entry}, u, \operatorname{false}\right), m\right)\right) = \operatorname{true})))) \land (\forall u: \operatorname{Source}, (\exists h: \operatorname{Word}, (\operatorname{Run}\left(\operatorname{step}, \operatorname{entry}, u, h, \operatorname{ready}\left(\operatorname{true}, \operatorname{rootBytes}\right)\right)) \iff u = \operatorname{of}\left(\operatorname{true}\right))) \land (\forall u: \operatorname{Source}, (\forall j: \operatorname{Nat}, (\operatorname{literalRecord}\left(\{\operatorname{emptyAddress}\}, \operatorname{iterate}\left(\operatorname{substitution}, j, u\right)\right) = \operatorname{rootLabel})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.selected_producer_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The single native selected machine has the effective complete control implementation above. Every legal finite returning history has its actual successful validation Read, and its whole retained row decodes to the literal record of its actual selected cut on that same validation source. Only local observer instructions, independent writer updates and the separate Return follow validation. Every finite source returns under every schedule with finitely many active writer updates. The continuation starts from the actual interrupted state after the final update, retaining its cursor and saved replies. The entire ready root row has invocation source support exactly the singleton alpha. The root literal record itself is compatible with every source and every substitution iterate, so the selected cut retains the distinction. Ready retains the selected cut and whole row and has no Work constructor or stored execution archive. These are finite cell and accessible state statements; physical allocator erasure is not asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.effective_selected_machine`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodeState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.encodedOp`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.finiteInstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.numericInstruction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.selected_producer_contract`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRARecordSoundness](NativeSelectedRARecordSoundness.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSelectedRA](../NativeSelectedRA.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformInput](../NativeUniformInput.md)
