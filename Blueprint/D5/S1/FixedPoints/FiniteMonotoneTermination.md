# Finite Monotone Termination

## Abstract

Finite monotone refinement terminates, while its limiting fixed point need not be unique.

**Theorem 1.1 (Finite monotone termination with nonunique limits).**

$$(\forall alpha: \operatorname{Type}, [\operatorname{Finite}(alpha)], [\operatorname{PartialOrder}(alpha)],\ update: \operatorname{OrderHom}\left(alpha, alpha\right), initial: alpha,\ (\forall state: alpha, \operatorname{update}\left(state\right) \leq state) \Rightarrow\\\exists N\in \mathbb{N}, \operatorname{IsFixedPt}\left(update, \operatorname{iterate}\left(update, N, initial\right)\right) \land \forall n\in \mathbb{N}, N \leq n \Rightarrow \operatorname{iterate}\left(update, n, initial\right) = \operatorname{iterate}\left(update, N, initial\right)) \land\\(\exists x, y: Bool, x \neq y \land (\forall n\in \mathbb{N}, \operatorname{iterate}\left(id, n, x\right) = x) \land (\forall n\in \mathbb{N}, \operatorname{iterate}\left(id, n, y\right) = y) \land \operatorname{IsFixedPt}\left(id, x\right) \land \operatorname{IsFixedPt}\left(id, y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/FiniteMonotoneTermination.finite_monotone_termination_and_nonunique_example` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be a finite partial order and let `update` be a monotone endomorphism. The hypothesis `update state <= state` orients strict refinement downward: whenever an update is not fixed, antisymmetry makes that step strictly smaller.

The iterates from any initial state form an antitone chain. Pinned Mathlib's `WellFoundedLT.antitone_chain_condition`, together with the finite-order well-founded instance, gives an index after which the chain is constant. Equality at the next index states that the reached value is a fixed point.

The uniqueness implication is refuted constructively in the same declaration. The identity update on `Bool` is monotone; the distinct initial states `false` and `true` remain at distinct fixed points under every iterate.

Repository search found a finite-set contraction specialization but no generic finite-poset wrapper. The proof therefore directly reuses the exact pinned antitone-chain theorem rather than reproving finite stabilization.

## References

- Truth anchor: `D5/S1/FixedPoints/FiniteMonotoneTermination.finite_monotone_termination_and_nonunique_example`
