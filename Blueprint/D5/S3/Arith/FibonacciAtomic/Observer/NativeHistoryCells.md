# NativeHistoryCells

## Abstract

NativeHistoryCells

**Definition 1.1 (Finite old-class pattern tuples).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Patterns`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Patterns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each actually appearing old class chooses one finite depth-d pattern. The tuple type has a finite enumeration. Repeated occurrences of one class share its entire pattern and variable family.

**Definition 1.2 (Class and reached-position variable names).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Variables`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Variables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum records the old class and exactly its reached frontier position. Equal ground values are allowed at different names; old class values alone must satisfy the full legal inequality relation.

**Definition 1.3 (Symbolic entire retained row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.wholeTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.wholeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expand every occurrence of an old class with the same class-indexed pattern term. Concrete exterior leaves remain literal and original absent-cut guards cannot be removed.

**Definition 1.4 (Native source-defined observation depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.requiredDepth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.requiredDepth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The depth is exactly one plus the maximum of zero, all new-cut address lengths and all historical physical-address lengths. Epochs and hidden source size do not enter it.

**Definition 1.5 (Tuple decomposition inverse).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.valuesEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.valuesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit splitValues map decomposes every old class through depthEquiv; rawValues reconstructs every class by filling. Both directions are inverse, including empty class and variable types.

**Definition 1.6 (Source-free invariant history test).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.testHistory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.testHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the complete finite mixed-epoch history on the fixed all-alpha filling of the finite whole term. This is a symbolic test only and does not assert that its filling is a legal or acquired source.

**Definition 1.7 (Finite complete feasibility enumeration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.feasiblePatterns`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.feasiblePatterns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Enumerate all old-class pattern tuples and retain those passing the invariant history test and every syntactic old disequality. Each cell contains its entire legal valuation fiber without size bounds or representative restriction; ground cells may be singleton.

**Theorem 1.8 (Exact nonempty entire cell test).**

$$\forall C: LiteralRow, (\forall d: Nat, (\forall eta: \operatorname{Patterns}\left(C, d\right), (\forall H: History, ((\forall e: \operatorname{Prod}\left(Nat, \operatorname{Prod}\left(Address, Reply\right)\right), ((e \in H) \implies (\operatorname{length}\left(\operatorname{fst}\left(\operatorname{snd}\left(e\right)\right)\right) < d))) \implies ((\operatorname{feasible}\left(eta, H\right) = true) \iff (\exists v: \operatorname{Variables}\left(eta\right) \to Source, (\operatorname{LegalFilling}\left(eta, H, v\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.cell_feasibility_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean test passes exactly when some whole valuation satisfies all old-class inequalities and every historical reply. Simultaneous finite ground separation supplies the sufficiency proof. Contradictory histories are total preprocessing inputs, without a service nonemptiness premise.

**Definition 1.9 (Exact native whole-fiber coproduct).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.historyCellEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.historyCellEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SLH.74.8 is an explicit equivalence from the coproduct of all feasible entire legal filling fibers to every actual original source with the retained canonical old row and complete history. Each cell valuation domain imposes only all old inequalities; the finite feasible-pattern test already guarantees history for every filling. cellSource reconstructs the original; sourceCell recovers every class and its unique pattern/frontier subtrees. No U2-U8 conclusion is assumed.

**Definition 1.10 (Whole-cell exact new-row interface).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.recutCell`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.recutCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At requiredDepth Q H, apply fieldwise symbolic recutting to wholeTerm using both its proved residual-depth guard and the derived Q length bound; neither guard is passed as a caller assumption. The output includes the actual independent record, reached order and actual new subtrees. canonicalRow_record_iff relates that record to the actual canonical Q row. This U1 interface is not the full finite-budget Theorem74.4: unification completeness, serial operational replay, decoding, certificate budgets, GB and the four equivalence directions remain separate obligations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Patterns`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.Variables`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.cell_feasibility_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.feasiblePatterns`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.historyCellEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.recutCell`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.requiredDepth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.testHistory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.valuesEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.wholeTerm`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers](NativeCutFibers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting](NativeSymbolicRecutting.md)
