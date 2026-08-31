# Commuting Closure Common Fixed Point

## Abstract

Two commuting closure operators compose to a closure whose fixed points are exactly their common fixed points.

**Theorem 1.1 (Commuting Composition Apply).**

$$\forall alpha: Type, first: ClosureOperator alpha, second: ClosureOperator alpha, x: alpha, [\operatorname{PartialOrder}\left(alpha\right)],\\{}(Function.Commute first second) \Rightarrow\\{}(commutingComposition first second commute x = first (second x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commutingComposition_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem establishes commuting composition apply in the module's typed setting.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Commuting Closure Composition Fixed iff).**

$$\forall alpha: Type, first: ClosureOperator alpha, second: ClosureOperator alpha, x: alpha, [\operatorname{PartialOrder}\left(alpha\right)],\\{}(Function.Commute first second) \Rightarrow\\{}(commutingComposition first second commute x = x \Leftrightarrow first x = x \land second x = x).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commuting_closure_composition_fixed_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point is fixed by the commuting composition exactly when it is fixed by both constituent closures.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Commuting Composition Order Independent).**

$$\forall alpha: Type, first: ClosureOperator alpha, second: ClosureOperator alpha, x: alpha, [\operatorname{PartialOrder}\left(alpha\right)],\\{}(Function.Commute first second) \Rightarrow\\{}(commutingComposition first second commute x = commutingComposition second first commute.symm x).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commuting_composition_order_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Commutativity makes the one-pass common closure independent of order.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commutingComposition_apply`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commuting_closure_composition_fixed_iff`
- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint.commuting_composition_order_independent`
