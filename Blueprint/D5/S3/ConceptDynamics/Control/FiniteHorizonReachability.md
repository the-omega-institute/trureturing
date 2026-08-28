# Finite-Horizon Reachability

## Abstract

Finite winning stages exactly characterize strategies that force the goal within the stated transition bound.

**Theorem 1.1 (Winning-stage membership is bounded strategic reachability).**

$$\forall X: Type, U: X \to Type,\\{}G: \operatorname{Set}\left(X\right), W: Nat \to \operatorname{Set}\left(X\right),\\{}R: \forall x, U(x) \to \operatorname{Set}\left(X\right), \forall x, u \in U(x), R_{u} \neq \emptyset,\\{}\operatorname{CPre}\left(S\right) = \{x : \exists u \in U(x), R_{u} \subseteq S\},\\{}W_{0} = G, W_{n+1} = \operatorname{union}\left(W_{n}, \operatorname{CPre}\left(W_{n}\right)\right),\\{}\forall n, x, x \in W_{n} \iff \operatorname{BoundedReachStrategy}\left(R, G, n, x\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.finite_horizon_reachability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each state, the control system provides a type of available actions. Each action has a nonempty set of possible successor states, so the environment may choose any successor after the action is selected.

The controlled predecessor of a target contains exactly the states with an action whose every possible successor lies in that target. The winning stages start at the goal and repeatedly adjoin this predecessor.

Independently, a bounded strategy is an inductive certificate. It either records that the current state is already in the goal or selects an action and provides a continuation certificate for every successor.

Induction on the horizon translates stage membership into this strategy certificate and back. Repository, pinned-library, Loogle, and LeanSearch checks found no exact theorem to reuse.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/FiniteHorizonReachability.finite_horizon_reachability`
