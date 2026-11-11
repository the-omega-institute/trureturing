# The entire proper-cone state base

## Abstract

A strictly positive mass gives the entire compact convex spanning state base.

This supplies the entire compact state base required in Quantum Origin V, definitions 79.1 and 79.2, from the original closed generating cone and original strictly positive mass. No self-duality, Jordan representation, preferred coordinates, or interior stationary state is assumed.

**Definition 1.1 (The full normalized cone base).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] \forall C \in \operatorname{ProperCone}\left(\operatorname{Real}\left(\right), A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{base}\left(C, u\right) = \operatorname{setOf}\left({x:A}\mapsto \operatorname{Mem}\left(x, C\right) \land u\left(x\right) = 1\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/ProperConeMassBase.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

base(C,u) is exactly the set of all x in C with u(x)=1. It is not a chosen frame, a finite sample, or an interior subset.

**Theorem 1.2 (Compactness, nonemptiness, convexity and full span).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{Nontrivial}\left(A\right)] \forall C \in \operatorname{ProperCone}\left(\operatorname{Real}\left(\right), A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{span}\left(\operatorname{Real}\left(\right), C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right) \Rightarrow \left(\left(\forall x \in A,\; \operatorname{Mem}\left(x, C\right) \Rightarrow \left(x \neq 0 \Rightarrow 0 < u\left(x\right)\right)\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{base}\left(C, u\right)\right) \land \left(\operatorname{IsCompact}\left(\operatorname{base}\left(C, u\right)\right) \land \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), \operatorname{base}\left(C, u\right)\right) \land \operatorname{span}\left(\operatorname{Real}\left(\right), \operatorname{base}\left(C, u\right)\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\operatorname{Real}\left(\right), A\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/ProperConeMassBase.entire_base_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A proper cone here is Mathlib closed cone data; strict positivity on every nonzero cone element also excludes a line. Generating means real linear span equals the entire nonzero carrier. Normalize any nonzero cone element to obtain a state. On the cone intersection with the unit sphere, compactness and strict positivity give a positive minimum of u. It bounds every normalized state in norm. Closedness then gives compactness. Each nonzero positive vector is its mass times a normalized state, so the entire base spans.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/ProperConeMassBase.base`
- Truth anchor: `D5/S3/Quantum/Analysis/ProperConeMassBase.entire_base_geometry`
- Dependency: [D5/S3/Quantum/Analysis/CompactConvexFixedState](CompactConvexFixedState.md)
