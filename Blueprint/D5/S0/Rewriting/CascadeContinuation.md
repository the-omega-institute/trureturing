# Cascade Continuation

## Abstract

A relation extendable at every state admits a path through every finite stage.

**Theorem 1.1 (Every stage has a coherent successor).**

$$(\forall s, \exists t, step(s, t)) \Rightarrow \exists path, path(0) = start \land \forall n, step(path(n), path(n+1)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/CascadeContinuation.cascade_continues_to_all_stages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source atom supplies a successor at every state. Choosing one such successor uniformly and iterating that choice produces a single stage-indexed path whose adjacent states satisfy the relation.

Pinned Mathlib supplies the iteration identities used to verify the initial and successor stages, but it has no declaration that builds this path from the local existence premise. The proof is therefore a new assembly of choice and iteration rather than a wrapper.

## References

- Truth anchor: `D5/S0/Rewriting/CascadeContinuation.cascade_continues_to_all_stages`
