# Weakest Preconditions

## Abstract

Weakest preconditions are inverse images and have the largest guaranteeing domain.

**Theorem 1.1 (Weakest preconditions characterize every guaranteeing domain).**

$$\forall X, Y: \operatorname{Type},\ F: X \to Y,\ P \subseteq X, Q \subseteq Y,\ ({\forall x\in P, F(x)\in Q} \iff P \subseteq \operatorname{wp}_{F}(Q)) \land\\(\forall R \subseteq X, {\forall x\in R, F(x)\in Q} \Rightarrow R \subseteq \operatorname{wp}_{F}(Q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/WeakestPrecondition.wp_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a process F and target set Q, wp_F(Q) is defined as the inverse image of Q. A predicate P guarantees Q after F exactly when P is contained in this inverse image.

The second clause quantifies over every other guaranteeing set R and places it inside wp_F(Q). This is the precise largest-domain, hence logically weakest, part of the source claim.

Repository searches found no weakest-precondition declaration. Pinned Mathlib's Set.mapsTo_iff_subset_preimage is the exact pointwise characterization and is applied by the proof; Mathlib does not package the additional largest-domain clause.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/WeakestPrecondition.wp_minimal`
