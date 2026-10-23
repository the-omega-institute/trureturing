# NativeControlConjugacy

## Abstract

NativeControlConjugacy

The native interpreter carries a complete control, an update epoch, one actual Source, and an appended chronological Event list. A control equivalence changes only the complete control. mapOp preserves localStep, the entire Read literal and reply continuation, applyRho, and the fixed Stop payload. reindex decodes an installed control through the inverse equivalence and applies this instruction map. mapConfig leaves the epoch, actual source and full log untouched.

advance is nativeStep on an optional configuration and keeps none absorbing. Its n-fold iteration counts n chronological actions, including all root Reads. Remaining means that an actual finite Run reaches its first Stop after exactly n actions. The interpreter is deterministic: two terminating runs from the same control, epoch and actual source have the same event list and payload.

CostModel assigns a cost to each complete address, each raw Read response and the constant Update acknowledgement. Its five coordinates are primitive calls, Reads, Updates, address costs and response costs. Each Read contributes one primitive and one Read; each Update contributes one primitive and one Update. localStep contributes zero to these five primitive coordinates while remaining in the event trace. In a program with zero internal actions, remaining actions and remaining primitives agree. No absolute application-specific bill is asserted.

**Theorem 1.1 (Exact native conjugacy).**

$$\forall C: Type, (\forall E: Type, (\forall O: Type, (\forall e: \operatorname{Equiv}\left(C, E\right), (\forall f: (C) \to (\operatorname{Op}\left(C, O\right)), ((\forall c: C, (\operatorname{reindex}\left(e, f, \operatorname{e}\left(c\right)\right) = \operatorname{mapOp}\left(e, \operatorname{f}\left(c\right)\right))) \land ((\forall x: \operatorname{Config}\left(C\right), (\operatorname{nativeStep}\left(\operatorname{reindex}\left(e, f\right), \operatorname{mapConfig}\left(e, x\right)\right) = \operatorname{map}\left(\operatorname{nativeStep}\left(f, x\right), \operatorname{mapConfig}\left(e\right)\right))) \land ((\forall c: C, (\forall j: Nat, (\forall u: Source, (\forall t: Trace, (\forall o: O, ((\operatorname{Run}\left(\operatorname{reindex}\left(e, f\right), \operatorname{e}\left(c\right), j, u, t, o\right)) \iff (\operatorname{Run}\left(f, c, j, u, t, o\right)))))))) \land ((\forall x: \operatorname{Config}\left(C\right), (\forall y: \operatorname{Config}\left(C\right), (\forall n: Nat, ((\operatorname{iterate}\left(\operatorname{advance}\left(\operatorname{reindex}\left(e, f\right)\right), n, \operatorname{some}\left(\operatorname{mapConfig}\left(e, x\right)\right)\right) = \operatorname{some}\left(\operatorname{mapConfig}\left(e, y\right)\right)) \iff (\operatorname{iterate}\left(\operatorname{advance}\left(f\right), n, \operatorname{some}\left(x\right)\right) = \operatorname{some}\left(y\right)))))) \land ((\forall c: C, (\forall o: O, ((\operatorname{reindex}\left(e, f, \operatorname{e}\left(c\right)\right) = \operatorname{stop}\left(o\right)) \iff (\operatorname{f}\left(c\right) = \operatorname{stop}\left(o\right))))) \land ((\forall c: C, (\forall j: Nat, (\forall u: Source, (\forall n: Nat, (\forall o: O, ((\operatorname{Remaining}\left(\operatorname{reindex}\left(e, f\right), \operatorname{e}\left(c\right), j, u, n, o\right)) \iff (\operatorname{Remaining}\left(f, c, j, u, n, o\right)))))))) \land ((\forall c: C, (\forall j: Nat, (\forall u: Source, (\forall t: Trace, (\forall s: Trace, (\forall o: O, (\forall b: O, ((\operatorname{Run}\left(f, c, j, u, t, o\right)) \implies ((\operatorname{Run}\left(f, c, j, u, s, b\right)) \implies ((t = s) \land (o = b))))))))))) \land (\forall c: C, (\forall j: Nat, (\forall u: Source, (\forall t: Trace, (\forall s: Trace, (\forall o: O, (\forall b: O, (\forall m: CostModel, ((\operatorname{Run}\left(f, c, j, u, t, o\right)) \implies ((\operatorname{Run}\left(\operatorname{reindex}\left(e, f\right), \operatorname{e}\left(c\right), j, u, s, b\right)) \implies ((t = s) \land ((o = b) \land (\forall i: \operatorname{Fin}\left(5\right), (\operatorname{cost}\left(m, t, i\right) = \operatorname{cost}\left(m, s, i\right))))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeControlConjugacy.native_control_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the actual finite Run preserves every event and the Stop payload. A separate one-step calculation preserves the source successor and appended event. Equal-step iteration gives exact finite prefixes, including empty reachability fibers. The inverse control equivalence supplies both implications. NativeSerialDepth.run_unique compares any two terminating runs from the same control, epoch and source. Applying that result after inverse run transport gives equality of the chronological traces and fixed halt payloads, and hence equality of all five charged coordinates even when the two traces are supplied independently.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeControlConjugacy.native_control_conjugacy`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](NativeSerialDepth.md)
