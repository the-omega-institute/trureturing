# Convex Mixture Closure

## Abstract

A convex family is closed under every binary convex mixture.

**Theorem 1.1 (Convex mixtures remain in a convex family).**

$$\operatorname{Convex}_{\mathbb{R}}(F) \land x, y \in F \land c \in [0, 1] \Rightarrow c \cdot x + (1 - c) \cdot y \in F.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/OperatorMeans/ConvexMixtureClosure.convex_mixture_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a real module and let F be a convex family in E. If x and y belong to F and c lies in the closed unit interval, then the binary mixture c x + (1-c) y also belongs to F.

This closes only the convex-mixture clause of pzg-v170 remark/27.702. It applies to a family of operator means once that family's convexity has been supplied; it does not establish Kubo--Ando convexity, identify the numerical root c-star, prove the monotonic mean chain, or claim transcendence.

Repository searches found no equivalent D5 operator-mean declaration. Direct search of the pinned Mathlib source found that Convex itself supplies binary-combination closure. The Lean theorem is a thin wrapper converting membership in the unit interval into two nonnegative weights whose sum is one.

## References

- Truth anchor: `D5/S3/Quantum/OperatorMeans/ConvexMixtureClosure.convex_mixture_mem`
