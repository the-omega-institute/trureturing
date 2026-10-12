# Stable-Core Observations and Exact Prefix Coding

## Abstract

A period of a discrete observation on the stable core gives a uniform exact tail; a positive period and finite alphabet give a finite range of entire forward names.

**Definition 1.1 (All forward images, including time zero).**

$$\begin{aligned}\forall X: Type, \forall f: X \Rightarrow X,\\\operatorname{stableCore}(f)=\operatorname{Intersection}(\operatorname{iterateRanges}(f))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Shadowing/StableCoreObservation.stableCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

stableCore(f) is the intersection, over all natural n including zero, of range(f^[n]). The dynamics may be nononto. The definition makes no exchange of an image with an intersection.

**Theorem 1.2 (A core observation period escapes to one uniform tail).**

$$\begin{aligned}\forall X: Type, \forall D: Type, [\operatorname{TopologicalSpace}(X)] [\operatorname{CompactSpace}(X)] [\operatorname{TTwoSpace}(X)]\\{[\operatorname{TopologicalSpace}(D)]} [\operatorname{DiscreteTopology}(D)] \\\forall f: X \Rightarrow X, \forall q: X \Rightarrow D, \forall M: Nat,\\{\operatorname{Continuous}(f)} \Rightarrow\\{\operatorname{Continuous}(q)} \Rightarrow\\{\forall a\in\operatorname{stableCore}(f), \operatorname{q}(\operatorname{iterate}(f, M, a))=\operatorname{q}(a)} \Rightarrow\\\exists N: Nat, \forall n: Nat, N\le n \Rightarrow \forall x: X, \operatorname{q}(\operatorname{iterate}(f, n+M, x))=\operatorname{q}(\operatorname{iterate}(f, n, x))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_eventually_periodic_of_stable_core_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X:Type u be compact Hausdorff and D:Type v discrete, with independent arbitrary universes. Let f:X→X and q:X→D be continuous. For any natural M, assume q(f^[M](a))=q(a) for every a in stableCore(f). Then there exists one natural N such that, for every n≥N and every x in X, q(f^[n+M](x))=q(f^[n](x)). Neither finiteness of D nor positivity of M is needed.

Put C={a:q(f^[M](a))≠q(a)}. The mismatch subset of D×D is closed because D is discrete, so continuity makes C closed. Every iterate image is compact and closed, and the sets C∩range(f^[n]) decrease. If each were nonempty, Mathlib's compact nested-intersection theorem would give a point in C∩stableCore(f), contradicting the core hypothesis. Thus the mismatch is absent from one whole image range(f^[N]). For n≥N, factor the iterate as f^[N] composed with f^[n-N] to place every f^[n](x) in that image. Applying the absence of mismatch there gives the claimed exact equality.

The finite whole-name theorem below consumes this supplier together with exact prefix injectivity. This theorem supplies a uniform tail, rather than assuming one or assuming finite whole names.

**Theorem 1.3 (The exact N+M prefix determines every whole name).**

$$\begin{aligned}\forall X: Type, \forall D: Type, \forall f: X \Rightarrow X, \forall q: X \Rightarrow D,\\\forall N: Nat, \forall M: Nat,\\{0<M} \Rightarrow\\{\forall n: Nat, N\le n \Rightarrow \forall x: X, \operatorname{q}(\operatorname{iterate}(f, n+M, x))=\operatorname{q}(\operatorname{iterate}(f, n, x))} \Rightarrow\\\operatorname{Injective}(\operatorname{prefix}(\operatorname{Set.range}(\operatorname{nu}(f, q)), N+M))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.forward_name_prefix_injective_of_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types X and D, arbitrary f and q, and naturals N,M with 0<M, assume the uniform tail equality for all n≥N and all x. Write nu(f,q)(x)(n)=q(f^[n](x)). Then the map from Set.range(nu(f,q)) to (Fin(N+M)→D), taking w to (i↦w(i)), is injective. This is a map on actual entire names, with all transient initial points and time zero retained. No topology, finiteness or nonemptiness is assumed in this theorem.

Given two names with the same prefix, use strong induction on k. For k<N+M use the prefix coordinate. Otherwise j=k-M satisfies N≤j and j<k because M>0. Both names have the same value at k as at j, so the induction hypothesis at j proves equality. Function and subtype extensionality give injectivity. The finite whole-name theorem consumes this induction result.

**Theorem 1.4 (Whole-name finiteness and a cardinal bound).**

$$\begin{aligned}\forall X: Type, \forall D: Type, [\operatorname{TopologicalSpace}(X)] [\operatorname{CompactSpace}(X)] [\operatorname{TTwoSpace}(X)]\\{[\operatorname{TopologicalSpace}(D)]} [\operatorname{DiscreteTopology}(D)] [\operatorname{Finite}(D)]\\\forall f: X \Rightarrow X, \forall q: X \Rightarrow D, \forall M: Nat,\\{\operatorname{Continuous}(f)} \Rightarrow\\{\operatorname{Continuous}(q)} \Rightarrow\\{0<M} \Rightarrow\\{\forall a\in\operatorname{stableCore}(f), \operatorname{q}(\operatorname{iterate}(f, M, a))=\operatorname{q}(a)} \Rightarrow\\\exists N: Nat, {\forall n: Nat, N\le n \Rightarrow \forall x: X, \operatorname{q}(\operatorname{iterate}(f, n+M, x))=\operatorname{q}(\operatorname{iterate}(f, n, x))} \land \operatorname{Injective}(\operatorname{prefix}(\operatorname{Set.range}(\operatorname{nu}(f, q)), N+M)) \land\\\operatorname{Set.Finite}(\operatorname{Set.range}(\operatorname{nu}(f, q))) \land \operatorname{Nat.card}(\operatorname{Set.range}(\operatorname{nu}(f, q)))\le \operatorname{Nat.card}(D)^{N+M}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_names_of_stable_core_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

With the compact Hausdorff and continuous telescope of the tail theorem, additionally require Finite D and 0<M. The result supplies a single N, its exact uniform tail equality, injectivity of the prefix map to Fin(N+M)→D, Set.Finite of the entire forward-name range, and Nat.card(range(nu(f,q)))≤Nat.card(D)^(N+M). These natural cards denote genuine finite cardinalities here: the prefix target is finite and injectivity proves the name subtype finite. The proof reuses Mathlib's finite-type injection and function-cardinality theorems.

If X is empty, its entire name range is empty and every assertion remains valid. If D is empty, the existence of q forces X empty; N+M>0 makes the stated bound compatible with the empty alphabet. No Nonempty instance, onto dynamics, recurrent-state pruning, or positive global period of f is used.

This supplies the first stage of the stable-core resolution R: every later finite joint observation whose core period is established gets a finite exact-name state space. Still required are onto core dynamics, observation periods from forward equicontinuity, the relative zero-dimensional resolution, the orbit lift and exact stable-image identification, the full all-observation diagram with whole-path lifting and inverse-limit conjugacy, and shadowing of the extension. R as a whole and unrestricted Peng Questions 5.1 and 5.2 are not formalized by this supplier. The elementary compactness and induction arguments carry no literature originality or worldwide-open claim.

All declarations have utility kind none: these are abstract compactness and induction results, not a finite certified instance, enumeration, checker or numerical reduction. The S1 whole-name expression is the definitional expansion of the existing S3 completeItinerary; no reverse-stratum import or duplicate named definition is introduced.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_eventually_periodic_of_stable_core_periodic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_names_of_stable_core_periodic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.forward_name_prefix_injective_of_eventually_periodic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.stableCore`
