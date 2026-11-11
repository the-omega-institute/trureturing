# Compact convex fixed states and the entire real fixed dual

## Abstract

Invariant compact convex sets contain fixed states and the full fixed dual forces uniqueness.

These are the general invariant-set and real-dual predecessors used by the asynchronous maximum argument for Quantum Origin V, Section 79. The matrix-only ChannelFixedState result is not substituted for the arbitrary real carrier. All topological statements concern the displayed finite-dimensional real norm topology.

**Theorem 1.1 (Fixed points inside invariant compact convex sets).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall B \in \operatorname{Set}\left(A\right),\; \operatorname{IsCompact}\left(B\right) \Rightarrow \left(\operatorname{Nonempty}\left(B\right) \Rightarrow \left(\operatorname{Convex}\left(\operatorname{Real}\left(\right), B\right) \Rightarrow \left(\operatorname{MapsTo}\left(Phi, B, B\right) \Rightarrow \left(\exists x \in A,\; \operatorname{Mem}\left(x, B\right) \land Phi\left(x\right) = x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CompactConvexFixedState.exists_fixed_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Phi is any real linear endomorphism of a finite-dimensional real normed space. Each nonempty compact convex invariant B contains a fixed point. Orbit Cesaro averages stay in B. The pinned Mathlib Birkhoff-average endpoint estimate tends to zero, and compactness supplies a subsequential fixed limit. No fixed-point theorem or mixing premise is added.

**Theorem 1.2 (Every fixed vector has its original scalar mass).**

$$\forall vA \in \operatorname{Universe}\left(\right),\; \forall A \in \operatorname{Type}\left(vA\right),\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\operatorname{Real}\left(\right), A\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}\left(\right), A\right)] \forall Phi \in \operatorname{LinearMap}\left(\operatorname{Real}\left(\right), A, A\right),\; \forall u \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(u, Phi\right) = u \Rightarrow \left(\left(\forall f \in \operatorname{Dual}\left(\operatorname{Real}\left(\right), A\right),\; \operatorname{comp}\left(f, Phi\right) = f \Rightarrow \left(\exists c \in \operatorname{Real}\left(\right),\; f = \operatorname{smul}\left(c, u\right)\right)\right) \Rightarrow \left(\forall sigma \in A,\; Phi\left(sigma\right) = sigma \Rightarrow \left(u\left(sigma\right) = 1 \Rightarrow \left(\forall x \in A,\; Phi\left(x\right) = x \Rightarrow x = \operatorname{smul}\left(u\left(x\right), sigma\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/CompactConvexFixedState.fixed_eq_mass_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The condition on f ranges over every real linear functional. Rank-nullity and the unchanged rank of the dual map bound the real fixed space by one dimension. A fixed sigma of mass one spans it, and applying the original u determines the scalar. Sigma may be on the cone boundary; this statement needs no cone or interior hypothesis.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/CompactConvexFixedState.exists_fixed_mem`
- Truth anchor: `D5/S3/Quantum/Analysis/CompactConvexFixedState.fixed_eq_mass_smul`
