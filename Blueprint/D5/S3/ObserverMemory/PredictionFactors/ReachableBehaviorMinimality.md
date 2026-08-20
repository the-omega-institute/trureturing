# Reachable Behavior Minimality

## Abstract

The reachable future-behavior quotient is the canonical smallest finite realization.

**Theorem 1.1 (The reachable behavior quotient is canonically minimal).**

$$\begin{gathered}\forall M, X, Xprime, B,\\[\operatorname{Monoid}(M)], [\operatorname{MulAction}(M, X)], [\operatorname{MulAction}(M, Xprime)],\\[\operatorname{Finite}(X)], [\operatorname{Finite}(Xprime)],\\a: X, ap: Xprime, O: X \to B, Op: Xprime \to B,\\Zbeta = \{m \cdot a \mid m \in M\} / (\forall k, O(k \cdot x) = O(k \cdot y)),\\(\forall xp, \exists m, m \cdot ap = xp) \land (\forall m, Op(m \cdot ap) = O(m \cdot a))\\\Rightarrow \operatorname{card}(Zbeta) \leq \operatorname{card}(Xprime) \land\\\exists! h: Xprime \to Zbeta, \operatorname{Surjective}\left(h\right) \land (\forall m, h(m \cdot ap) = [m \cdot a]).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.finite_state_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be the actual anchor for a monoid action on X, with public readout O. The carrier Zbeta is constructed by restricting to states m acting on a and quotienting two such states when every continuation k gives the same public readout.

Let Xprime be a finite competing carrier whose every state is reachable from its anchor and whose anchor readout agrees with the actual system after every action. There is a unique surjection from Xprime onto Zbeta sending each competing orbit point to the class of the corresponding actual orbit point.

The factor chooses an action reaching each competing state. Equal competing orbit points have equal readouts after every continuation, so their actual orbit points define the same behavior class. Pinned Mathlib's Nat.card_le_card_of_surjective then gives the finite-state lower bound directly.

The repository's controlled behavior universal property is close but assumes a supplied surjective realization and commuting structure; it does not derive the anchor-relative factor from this theorem's source hypotheses.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionFactors/ReachableBehaviorMinimality.finite_state_minimality`
