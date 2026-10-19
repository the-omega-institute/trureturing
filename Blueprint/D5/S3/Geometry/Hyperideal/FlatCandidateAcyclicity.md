# The flat-candidate dependency graph is acyclic

## Abstract

Positive shared lengths forbid directed cycles among flat-candidate dependencies.

Let Q be a type of globally shared opposite-edge labels. A candidate relation C(a,b,c) records that a flat candidate with distinguished pair a has the two other opposite pairs b and c. The directed edge relation sends a to both b and c.

Assume every label has a positive generalized length z, in the stronger form 1<z(a), and every candidate satisfies z(a) >= 1+z(b)+z(c). Then no nonempty transitive directed path can return to its starting label. Each edge strictly decreases z, so a return path would give z(a)<z(a). The conclusion is independent of volume maximality and keeps repeated labels as separate edge occurrences.

**Theorem 1.1 (Flat-candidate cycle exclusion).**

$$\forall Q \in Type,\; \forall z \in Function\left(Q, Real\right),\; \forall C \in Function\left(Q, Function\left(Q, Function\left(Q, Prop\right)\right)\right),\; \left(\left(\forall a \in Q,\; 1 < z\left(a\right)\right) \land \left(\forall a \in Q,\; \forall b \in Q,\; \forall c \in Q,\; C\left(a, b, c\right) \Rightarrow z\left(a\right) \ge 1 + z\left(b\right) + z\left(c\right)\right)\right) \Rightarrow -HasDirectedCycle\left(candidateEdge\left(C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FlatCandidateAcyclicity.flat_candidate_cycle_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first derives strict decrease along every directed edge from the positive summand 1+z(c), then composes the decrease along Relation.TransGen and closes the cycle by irreflexivity of < on the reals.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FlatCandidateAcyclicity.flat_candidate_cycle_exclusion`
