# Three-Read Action Obstruction

## Abstract

Every globally valid three-read protocol has unbounded literal atomic-action cost.

A source is a strictly positive rank-one real relation matrix. A protocol reads the empty word first, extends its literal word chronologically, and must terminate with the original relation.

For every valid protocol and every natural bound C, a positive shear fiber can be selected whose common first two readings force a third literal continuation with cost greater than C. The source supplied by that fiber still has a terminating run of at most three readings.

**Theorem 1.1 (No uniform finite action bound for three reads).**

$$\begin{aligned}\forall P, \operatorname{OriginalValid}\left(P\right) \Rightarrow \forall C\in\mathbb{N},\\{}\\\exists R, n, tr, out \operatorname{run}\left(P, R, n, tr, out\right) \land \operatorname{readsAtMost}\left(tr, 3\right) \land \operatorname{returns}\left(out, R\right) \land C < \operatorname{actualCost}\left(tr, out\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/SelfCalibratingActionObstruction.three_read_action_unbounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second query is a nontrivial integral shear. Choosing the shear fiber parameter z as the reciprocal of a prescribed natural scale makes the exact third-read lower bound exceed that scale.

The proof uses the full positive shear-fiber criterion: every compatible source has the same first two readings, and any successful third run pays the fixed prefix together with the required continuation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/SelfCalibratingActionObstruction.three_read_action_unbounded`
- Dependency: [D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers](SelfCalibratingFibers.md)
