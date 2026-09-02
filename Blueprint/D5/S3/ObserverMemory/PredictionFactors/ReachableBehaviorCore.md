# Reachable Behavior Core

## Abstract

The reachable future-behavior quotient is reached, separated by future protocols, stable under protocol prefixes, and universal among reachable realizations.

**Theorem 1.1 (The reachable behavior quotient has all four core properties).**

$$\begin{gathered}\forall M: \operatorname{Type}, X: \operatorname{Type}, B: \operatorname{Type},\\{}[\operatorname{Monoid}(M)], [\operatorname{MulAction}(M, X)], a: X, O: X \to B,\\{}(\operatorname{Surjective}\left((m \mapsto \operatorname{behaviorClass}\left(a, O, m\right))\right)) \land (\forall z1: \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right), z2: \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right), z1 \ne z2 \Rightarrow \exists c: M, \operatorname{kerLift}\left(\operatorname{futureBehavior}\left(a, O\right), z1, c\right) \ne \operatorname{kerLift}\left(\operatorname{futureBehavior}\left(a, O\right), z2, c\right)) \land\\{}(\forall p: M, \exists! U: \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right) \to \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right), \forall m: M, \operatorname{U}\left(\operatorname{behaviorClass}\left(a, O, m\right)\right) = \operatorname{behaviorClass}\left(a, O, p \cdot m\right)) \land\\{}(\forall Xprime: \operatorname{Type}, [\operatorname{MulAction}(M, Xprime)], aprime: Xprime, Oprime: Xprime \to B,\\{}(\forall xprime: Xprime, \exists m: M, m \cdot aprime = xprime) \land (\forall m: M, \operatorname{Oprime}\left(m \cdot aprime\right) = \operatorname{O}\left(m \cdot a\right)) \Rightarrow \exists! h: Xprime \to \operatorname{ReachableBehaviorQuotient}\left(M, a, O\right), \operatorname{Surjective}\left(h\right) \land (\forall m: M, \operatorname{h}\left(m \cdot aprime\right) = \operatorname{behaviorClass}\left(a, O, m\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorCore.reachable_behavior_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a monoid of allowed protocols act on a state carrier from an actual anchor, and let O be the public readout. The target is the existing quotient of reachable states by equality of every future readout.

Every quotient class is produced by an allowed protocol. Injectivity of the kernel lift makes distinct classes differ at some continuation, and left multiplication constructs the unique update induced by each protocol prefix.

For every other reachable action carrier with the same anchor behavior, there is a unique surjection to the quotient, determined on every orbit point by its canonical behavior class.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorCore.reachable_behavior_core`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/CanonicalReachableBehaviorFactor](CanonicalReachableBehaviorFactor.md)
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorClassSurjectivity](ReachableBehaviorClassSurjectivity.md)
