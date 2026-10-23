# NativeSymbolicRecutting

## Abstract

NativeSymbolicRecutting

**Definition 1.1 (Residual depth guard).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.DeepAt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.DeepAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every residual variable occurrence lies at or beyond the fixed original depth. This condition is proved for the whole native cell terms, not passed as a substitute for the source theorem.

**Theorem 1.2 (History constancy over every filling).**

$$\forall X: Type, (\forall d: Nat, (\forall t: \operatorname{Term}\left(X\right), ((\operatorname{DeepAt}\left(d, \operatorname{nil}\left(\right), t\right)) \implies (\forall H: History, ((\forall e: \operatorname{Prod}\left(Nat, \operatorname{Prod}\left(Address, Reply\right)\right), ((e \in H) \implies (\operatorname{length}\left(\operatorname{fst}\left(\operatorname{snd}\left(e\right)\right)\right) < d))) \implies (\forall test, v: X \to Source, ((\operatorname{Consistent}\left(H, \operatorname{evaluate}\left(test, t\right)\right)) \iff (\operatorname{Consistent}\left(H, \operatorname{evaluate}\left(v, t\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolic_history_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For histories whose physical addresses are shorter than d, all fillings give the same complete history test at every listed epoch. The fixed testing filling can violate old disequalities; it is used solely for this invariant test.

**Definition 1.3 (New holes separate from residual variables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.SymbolicExterior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.SymbolicExterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

New holes carry native addresses, while residual variables remain in a different sum constructor. Filling residuals never fills new holes.

**Definition 1.4 (Exact new reached order).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicOrdered`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicOrdered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter Q by finite symbolic navigation and sort the reached addresses lexicographically. No residual occurrence can be crossed before a tested cut ends.

**Definition 1.5 (Full symbolic record after filling).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicRecord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record includes the concrete filled exterior and all ordered reached pairs satisfying equality of their evaluated symbolic subterms. Nonmembership among reached pairs retains disequality.

**Theorem 1.6 (Exact fieldwise native recutting).**

$$\forall X: Type, (\forall d: Nat, (\forall Q: CutSet, (\forall t: \operatorname{Term}\left(X\right), (\forall v: X \to Source, (((\operatorname{CutPrefixFree}\left(Q\right)) \land (\forall q: Address, ((q \in Q) \implies (\operatorname{length}\left(q\right) < d))) \land (\operatorname{DeepAt}\left(d, \operatorname{nil}\left(\right), t\right))) \implies ((\operatorname{orderedHoles}\left(Q, \operatorname{evaluate}\left(v, t\right)\right) = \operatorname{symbolicOrdered}\left(Q, t\right)) \land (\operatorname{cutExterior}\left(Q, \operatorname{nil}\left(\right), \operatorname{evaluate}\left(v, t\right)\right) = \operatorname{exteriorFill}\left(v, \operatorname{symbolicExterior}\left(Q, \operatorname{nil}\left(\right), t\right)\right)) \land (\forall q: Address, ((q \in Q) \implies (\operatorname{subtree}\left(q, \operatorname{evaluate}\left(v, t\right)\right) = \operatorname{OptionMap}\left(\operatorname{evaluate}\left(v\right), \operatorname{termAt}\left(q, t\right)\right)))) \land (\operatorname{literalRecord}\left(Q, \operatorname{evaluate}\left(v, t\right)\right) = \operatorname{symbolicRecord}\left(Q, t, v\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolic_recut_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SLH.74.9 preserves reached ordering, the entire concrete exterior, every actual new-hole subtree and the complete finite partition. The result is the independent literalRecord of the actual filled original source. The existing canonicalRow_record_iff then fixes the exact canonical-row equality relation. Empty and root Q remain in scope.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.DeepAt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.SymbolicExterior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicOrdered`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolicRecord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolic_history_constant`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.symbolic_recut_exact`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation](NativeGroundSeparation.md)
