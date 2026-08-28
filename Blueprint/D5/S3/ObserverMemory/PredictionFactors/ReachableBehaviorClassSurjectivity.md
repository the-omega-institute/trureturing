# Reachable Behavior Class Surjectivity

## Abstract

Every class of the reachable future-behavior quotient is produced by an allowed action.

**Theorem 1.1 (Every reachable behavior class is reachable).**

$$\forall M, X, B, [\operatorname{Monoid}(M)], [\operatorname{MulAction}(M, X)], a: X, O: X \to B, \forall z: ReachableBehaviorQuotient(M, a, O), \exists m: M, behaviorClass(a, O, m) = z.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity.every_reachable_behavior_class_is_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the existing quotient of the actual anchor orbit by equality of every continued public readout.

Each quotient representative already contains an allowed action reaching its underlying state. That action produces the representative's canonical behavior class, so the behavior-class map is surjective.

The proof reuses the canonical reachable-behavior family and applies pinned Mathlib quotient surjectivity; it introduces no second orbit, behavior, or quotient definition.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity.every_reachable_behavior_class_is_reachable`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality](ReachableBehaviorMinimality.md)
