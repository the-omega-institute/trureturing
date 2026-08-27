# Canonical Reachable Behavior Factor

## Abstract

Every reachable realization of the same anchor behavior maps uniquely and surjectively to the canonical reachable behavior quotient.

**Theorem 1.1 (The reachable behavior factor is unique and surjective).**

$$\begin{gathered}\forall M, X, Xprime, B,\\{}[\operatorname{Monoid}(M)], [\operatorname{MulAction}(M, X)], [\operatorname{MulAction}(M, Xprime)],\\{}a: X, aprime: Xprime, O: X \to B, Oprime: Xprime \to B,\\{}(\forall xprime: Xprime, \exists m: M, m \cdot aprime = xprime) \land (\forall m: M, Oprime(m \cdot aprime) = O(m \cdot a))\\{}\Rightarrow \exists! h: Xprime \to \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right), \operatorname{Surjective}\left(h\right) \land\\{}(\forall m: M, h(m \cdot aprime) = \operatorname{behaviorClass}\left(a, O, m\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor.canonical_reachable_behavior_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let two monoid actions have actual anchors a and a', with public readouts O and O'. Every competing state is required to be reachable from a', and the two anchor readouts agree after every allowed action.

The target is the existing reachable behavior quotient: reachable source states are identified exactly when every continuation has the same public readout.

There is a unique surjection h from the competing carrier to that quotient, and h sends every point m acting on a' to the behavior class of m acting on a. Reachability makes this computation rule determine h on the whole competing carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor.canonical_reachable_behavior_factor`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality](ReachableBehaviorMinimality.md)
