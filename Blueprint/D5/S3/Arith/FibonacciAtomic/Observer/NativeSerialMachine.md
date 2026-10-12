# NativeSerialMachine

## Abstract

NativeSerialMachine

**Definition 1.1 (Source-free local instructions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Op`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Op` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transition function receives only control. Control may be infinite and may contain unbounded local workspace and all common retained inputs. Read returns exactly one four-valued physical reply. ApplyRho has no source-dependent return value. Stop returns the complete output.

**Definition 1.2 (Chronological physical actions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Event`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Event` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every local step and real update is recorded. Every Read invocation contributes one event, including repeated addresses. Epoch and address are literal descriptors of the physical call.

**Definition 1.3 (Chronological literal Read events).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.reads`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.reads` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filtering removes only local and update markers. It preserves chronological order and multiplicity. The length of this list is the raw-call cost.

**Definition 1.4 (Reply words and raw cost).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.answers`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.answers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reply word maps the chronological Read event list to its four-valued replies. Its length equals the number of Read invocations; local actions and updates contribute zero raw calls. In the formulas ReadEvent is Event.read, tuple is the displayed product constructor, iterate is Function.iterate, result is the final Sum component of Boundary, append is chronological list append, and IsPrefix is the list prefix relation.

**Definition 1.5 (Actual physical configuration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Config`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Config` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A configuration consists of source-free local control, certified epoch, one actual native source register and the complete retained action trace. Neither the register nor that trace is an argument of the local transition function.

**Definition 1.6 (Next observable boundary).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Boundary`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary records the exact control and actual epoch together with either the next physical address or the entire terminal output.

**Definition 1.7 (One actual register step).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.nativeStep`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.nativeStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is one physical source register. A local step changes control; Read inspects only its submitted address; ApplyRho substitutes the actual current tree and increments the certified epoch. The interpreter cannot inspect register size, shape, equality or timing.

**Definition 1.8 (Finite actual termination).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Run`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inductive rules retain every ordinary step, every true substitution update and every actual literal Read. Termination is sourcewise and supplies no uniform runtime or address bound.

**Definition 1.9 (Partial reply-word replay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Replay`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Replay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replay receives only a finite reply word. It follows the same local and update steps and stops when that word has been consumed at the next Read or Stop. Unreachable words may have no finite replay.

**Theorem 1.10 (Witness-independent replay).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall e: Nat, (\forall w: \operatorname{List}\left(Reply\right), (\forall t, s: Trace, (\forall b, d: \operatorname{Boundary}\left(C, O\right), ((\operatorname{Replay}\left(delta, c, e, w, t, b\right)) \implies ((\operatorname{Replay}\left(delta, c, e, w, s, d\right)) \implies ((t = s) \land (b = d))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.replay_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A reply word has at most one finite replay trace and boundary. Equality includes the control, epoch, next physical address or complete terminal output.

**Theorem 1.11 (Actual runs supply replay boundaries).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall e: Nat, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{Run}\left(delta, c, e, r, t, o\right)) \implies ((\exists next: C, (\exists epoch: Nat, (\operatorname{Replay}\left(delta, c, e, \operatorname{answers}\left(t\right), t, \operatorname{tuple}\left(next, epoch, \operatorname{inr}\left(o\right)\right)\right)))) \land (\forall n: Nat, (\forall a: Address, (\forall y: Reply, ((\operatorname{ReadEvent}\left(n, a, y\right) \in t) \implies (\exists w: \operatorname{List}\left(Reply\right), (\exists s: Trace, (\exists next: C, ((\operatorname{length}\left(w\right) < \operatorname{length}\left(\operatorname{answers}\left(t\right)\right)) \land (\operatorname{Replay}\left(delta, c, e, w, s, \operatorname{tuple}\left(next, n, \operatorname{inl}\left(a\right)\right)\right)))))))))) \land (\forall w: \operatorname{List}\left(Reply\right), (\forall s, z: Trace, (\forall b, d: \operatorname{Boundary}\left(C, O\right), ((\operatorname{Replay}\left(delta, c, e, w, s, b\right)) \implies ((\operatorname{Replay}\left(delta, c, e, w, z, d\right)) \implies ((s = z) \land (b = d)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.operational_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual terminating run supplies a full terminal replay and a finite replay boundary before each actual Read. Every such word is shorter than the terminal reply list. Replay uniqueness makes the descriptors independent of the source used to establish existence.

**Theorem 1.12 (Every reached prefix reaches its next boundary).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall e: Nat, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{Run}\left(delta, c, e, r, t, o\right)) \implies (\forall w: \operatorname{List}\left(Reply\right), ((\operatorname{IsPrefix}\left(w, \operatorname{answers}\left(t\right)\right)) \implies (\exists s: Trace, (\exists b: \operatorname{Boundary}\left(C, O\right), ((\operatorname{Replay}\left(delta, c, e, w, s, b\right)) \land (\operatorname{IsPrefix}\left(s, t\right)) \land (\operatorname{answers}\left(s\right) = w) \land ((w = \operatorname{answers}\left(t\right)) \iff (\operatorname{result}\left(b\right) = \operatorname{inr}\left(o\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.reached_prefix_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every prefix of a terminating run’s reply word has a finite source-free replay. Its full action trace is a prefix of the actual trace and has exactly the supplied replies. Its boundary is Stop with the actual output exactly when the whole reply word has been consumed. This is an existence result from an actual terminating source, not an effective stopping oracle.

**Theorem 1.13 (Certified physical evolution).**

$$\forall C, O: Type, (\forall delta: C \to \operatorname{Op}\left(C, O\right), (\forall c: C, (\forall e: Nat, (\forall r: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{Run}\left(delta, c, e, r, t, o\right)) \implies (\forall u: Source, ((r = \operatorname{iterate}\left(substitution, e, u\right)) \implies (\forall old: Trace, (\exists next: C, (\exists epoch: Nat, ((e \leq epoch) \land (\operatorname{Reaches}\left(\operatorname{nativeStep}\left(delta\right), \operatorname{tuple}\left(c, e, r, old\right), \operatorname{tuple}\left(next, epoch, \operatorname{iterate}\left(substitution, epoch, u\right), \operatorname{append}\left(old, t\right)\right)\right)) \land (\operatorname{delta}\left(next\right) = \operatorname{stop}\left(o\right)) \land (\forall n: Nat, (\forall a: Address, (\forall y: Reply, ((\operatorname{ReadEvent}\left(n, a, y\right) \in t) \implies (\operatorname{readout}\left(a, \operatorname{iterate}\left(substitution, n, u\right)\right) = y))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.actual_register_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting from the actual iterated original source at the certified epoch, execution reaches the actual iterated source at its final epoch, which is at least the initial epoch. Appending the full chronological trace to any retained prior trace is exact. Every Read is truthful at its actual epoch.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Boundary`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Config`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Event`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Op`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Replay`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.Run`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.actual_register_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.answers`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.nativeStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.operational_replay`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.reached_prefix_replay`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.reads`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.replay_deterministic`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
