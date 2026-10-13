# Stable Core and Complete Observation Names

## Abstract

A stable-image observation period extends to a uniform exact tail; positive periods over finite alphabets then give finitely many complete names.

**Theorem 1.1 (From the stable image to one uniform tail).**

$$\begin{aligned}\forall X: Type, \forall D: Type,\\{}[\operatorname{TopologicalSpace}(X)]\\{}[\operatorname{CompactSpace}(X)]\\{}[\operatorname{T2Space}(X)]\\{}[\operatorname{TopologicalSpace}(D)]\\{}[\operatorname{DiscreteTopology}(D)]\\\forall f: X \Rightarrow X, \forall q: X \Rightarrow D,\\\operatorname{Continuous}(f) \Rightarrow\\\operatorname{Continuous}(q) \Rightarrow\\\forall M: \mathbb{N},\\(\forall a \in \operatorname{Set.iInter}(n \mapsto \operatorname{Set.range}(\operatorname{Function.iterate}(f, n))), q(\operatorname{Function.iterate}(f, M)(a)) = q(a)) \Rightarrow\\\exists N: \mathbb{N}, (\forall n: \mathbb{N}, N \le n \Rightarrow \forall x: X, q(\operatorname{Function.iterate}(f, n+M)(x)) = q(\operatorname{Function.iterate}(f, n)(x)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_eventually_periodic_of_stable_core_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Dekui Peng (2026). *Shadowing in Dynamical Systems: Zero-dimensional Extensions and Inverse Limits*. URL: <https://arxiv.org/abs/2606.14435v3>.

*Commentary.*

Let X be compact Hausdorff, f:X→X continuous, D any discrete space, and q:X→D continuous. The stable image is the intersection of the exact iterate ranges f^n(X), with n=0 included. Assume q(f^M(a))=q(a) at every stable-image point. One natural N then satisfies q(f^(n+M)(x))=q(f^n(x)) simultaneously for every x and every n≥N. M may be zero, and D need not be finite. No metric, countability, surjectivity, invertibility or source-shadowing assumption is introduced.

The mismatch set B={x:q(f^M(x))≠q(x)} is closed because D is discrete. It misses the stable image by the supplied core law. If every proposed N failed, a violating point at a later iterate would belong to B and every earlier iterate range. The nested closed sets B∩f^n(X) would therefore have nonempty finite intersections; compactness would put a point in B and the stable image, a contradiction. This compactness argument constructs the uniform exact tail rather than assuming it.

This is a repository-derived supplier for a restricted stable-core resolution inspired by Peng's zero-dimensional extension questions. The source/interface review found no matching supplier in the reviewed project dynamics/topology modules or pinned Mathlib topology/dynamics scope. That bounded library search does not certify worldwide novelty. The unrestricted Questions 5.1 and 5.2, the relative quotient, orbit lift and final inverse-limit construction remain unfinished.

**Theorem 1.2 (Complete names are determined by a finite prefix).**

$$\begin{aligned}\forall X: Type, \forall D: Type,\\\forall f: X \Rightarrow X, \forall q: X \Rightarrow D,\\\forall N: \mathbb{N},\\\forall M: \mathbb{N},\\0 < M \Rightarrow\\(\forall n: \mathbb{N}, N \le n \Rightarrow \forall x: X, q(\operatorname{Function.iterate}(f, n+M)(x)) = q(\operatorname{Function.iterate}(f, n)(x))) \Rightarrow\\\operatorname{Set.InjOn}(w \mapsto (k: \operatorname{Fin}(N+M) \mapsto w(k)), \operatorname{Set.range}(x \mapsto (n \mapsto q(\operatorname{Function.iterate}(f, n)(x)))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_name_injective_of_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary types X and D, maps f and q, and a uniform tail law of positive period M, restriction to Fin(N+M) is injective on the exact range of complete names x↦(n↦q(f^n(x))). Neither topology nor finiteness of D is needed. Empty source and alphabet are retained. All times, including time zero and the transient segment before N, are observed.

Strong induction on a time k compares two names. Below N+M their prefix equality pays the coordinate. At every later time, the tail law reduces k to k−M, which is at least N and strictly smaller than k. This reduction supplies exact whole-name injectivity, rather than only a finite-prefix realization or a finite-graph language inclusion.

**Theorem 1.3 (A finite carrier of complete names).**

$$\begin{aligned}\forall X: Type, \forall D: Type,\\{}[\operatorname{TopologicalSpace}(X)]\\{}[\operatorname{CompactSpace}(X)]\\{}[\operatorname{T2Space}(X)]\\{}[\operatorname{TopologicalSpace}(D)]\\{}[\operatorname{DiscreteTopology}(D)]\\{}[\operatorname{Finite}(D)]\\\forall f: X \Rightarrow X, \forall q: X \Rightarrow D,\\\operatorname{Continuous}(f) \Rightarrow\\\operatorname{Continuous}(q) \Rightarrow\\\forall M: \mathbb{N},\\0 < M \Rightarrow\\(\forall a \in \operatorname{Set.iInter}(n \mapsto \operatorname{Set.range}(\operatorname{Function.iterate}(f, n))), q(\operatorname{Function.iterate}(f, M)(a)) = q(a)) \Rightarrow\\\operatorname{Set.Finite}(\operatorname{Set.range}(x \mapsto (n \mapsto q(\operatorname{Function.iterate}(f, n)(x)))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_range_finite_of_stable_core_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the compact Hausdorff continuous system, a finite discrete alphabet and a positive stable-image observation period give a finite exact range of complete names. The preceding uniform-tail theorem provides N, and prefix injection embeds the name subtype into the finite function type Fin(N+M)→D. Transient source points are included; no replacement by names beginning only on the stable core is made.

This finite carrier is the intended input to finite joint-observation stages and their all-time restriction bonds. The present module proves the carrier finiteness; it does not yet construct those stages, prove the orbit-range identity, or invoke the existing Mittag–Leffler shadowing theorem.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_eventually_periodic_of_stable_core_periodic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_name_injective_of_eventually_periodic`
- Truth anchor: `D5/S1/Dynamics/Shadowing/StableCoreObservation.finite_observation_range_finite_of_stable_core_periodic`
