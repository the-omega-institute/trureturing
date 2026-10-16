# Finite Complete Names and Initial-Point Tracing

## Abstract

Finitely many complete names for every finite continuous observation yield an actual finite open control cover and tracing by the initial point.

**Theorem 1.1 (Constructing the control cover).**

$$\begin{aligned}\forall X: Type,\\{}[\operatorname{TopologicalSpace}(X)]\\{}[\operatorname{CompactSpace}(X)]\\{}[\operatorname{T2Space}(X)]\\{}[\operatorname{TotallyDisconnectedSpace}(X)]\\\forall f: X \Rightarrow X,\\\operatorname{Continuous}(f) \Rightarrow\\(\forall m: \mathbb{N}, \forall q: X \Rightarrow \operatorname{Fin}(m), \operatorname{Continuous}(q) \Rightarrow \operatorname{Set.Finite}(\operatorname{Set.range}(x \mapsto (n \mapsto q(\operatorname{Function.iterate}(f, n)(x)))))) \Rightarrow\\\forall C: \operatorname{Finset}(\operatorname{Opens}(X)),\\\operatorname{IsOpenCover}(U: C \mapsto \operatorname{Subtype.val}(U)) \Rightarrow\\\exists D: \operatorname{Finset}(\operatorname{Opens}(X)), \operatorname{IsOpenCover}(U: D \mapsto \operatorname{Subtype.val}(U)) \land \forall a: \mathbb{N} \Rightarrow X, \operatorname{PseudoOrbit}(f, D, a) \Rightarrow \operatorname{Shadows}(f, C, a, a(0))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/FiniteObservationShadowing.initial_point_tracing_of_finite_observation_names` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Let X be compact Hausdorff and zero-dimensional, with continuous f:X→X. Assume that for each natural m and each continuous q:X→Fin m, the exact range of complete names x↦(n↦q(f^n(x))) is finite. For every finite open cover C, there is a finite open cover D such that every D-pseudo-orbit a is C-shadowed by a(0), simultaneously at all natural times including zero. IsOpenCover in the formula is applied to U↦U.val with U ranging over the indicated finset. PseudoOrbit and Shadows are the existing finite-open-cover contracts. The compact Hausdorff totally disconnected hypothesis supplies a clopen basis. There is no metric, countability, nonempty, surjectivity or invertibility assumption.

Refine C by a finite disjoint clopen partition W indexed by Fin m, using Mathlib's IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover. The unique cell containing x defines q(x); each cell is open, so q is locally constant and continuous. The existing continuous_observationName theorem makes the complete-name map continuous. Its range S is finite by hypothesis and Hausdorff as a subspace of the product of discrete alphabets; hence S is discrete. The inverse images of singleton names are open and form the finite cover D. This constructs D from the observations.

A D-controlled error pair f(a(n)),a(n+1) lies in one complete-name fiber, so their names are equal. The name of f(x) is the left shift of the name of x. Induction therefore identifies the complete names of a(n) and f^n(a(0)). At coordinate zero these points have the same partition label. Their common clopen cell lies inside one member of C, proving tracing. The proof includes empty sources and empty name images without choosing an initial point unless a pseudo-orbit is already supplied.

This repository-derived construction fills the inference between finite complete observations and finite-cover tracing. StableCoreObservation's finite_observation_range_finite_of_stable_core_periodic supplies the hypothesis when each finite continuous observation has a positive period on the stable image; the period may depend on that observation. Substituting this supplier and choosing a(0) as the tracing point gives HasShadowing. This application introduces no additional mathematical declaration. Neither it nor the present inference constructs a relative Boolean extension or resolves Peng's general Question 5.1.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/FiniteObservationShadowing.initial_point_tracing_of_finite_observation_names`
- Dependency: [D5/S1/Dynamics/Shadowing/CompactObservationSubshift](CompactObservationSubshift.md)
