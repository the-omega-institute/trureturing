# Centered open star refinements

## Abstract

Finite centered open star refinements of finite covers of compact Hausdorff spaces.

**Theorem 1.1 (Finite construction from continuous coordinates).**

$$\forall X \in Types,\; [TopologicalSpace\left(X\right)] [CompactSpace\left(X\right)] [TTwoSpace\left(X\right)] \forall n \in Nat,\; \forall V \in Fin\left(n\right) \to Set\left(X\right),\; \left(\forall j \in Fin\left(n\right),\; IsOpen\left(V\left(j\right)\right)\right) \Rightarrow \left(\left(\forall x \in X,\; \exists j \in Fin\left(n\right),\; x \in V\left(j\right)\right) \Rightarrow \left(\exists U \in X \to Set\left(X\right),\; \exists s \in Finset\left(X\right),\; \left(\forall c \in X,\; IsOpen\left(U\left(c\right)\right)\right) \land \left(\left(\forall c \in X,\; c \in U\left(c\right)\right) \land \left(\left(\forall x \in X,\; \exists c \in X,\; c \in s \land x \in U\left(c\right)\right) \land \left(\forall c \in X,\; c \in s \Rightarrow \left(\exists j \in Fin\left(n\right),\; \forall d \in X,\; d \in s \Rightarrow \left(Nonempty\left(Inter\left(U\left(c\right), U\left(d\right)\right)\right) \Rightarrow Subset\left(U\left(d\right), V\left(j\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteCenteredStarRefinement.exists_finite_centered_star_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is any compact Hausdorff topological space. The original cover V has n members indexed by Fin(n). The natural number n may be zero, in which case the covering hypothesis forces X to be empty. Set and Finset denote subsets and finite subsets. Inter, Subset and Nonempty have their ordinary set-theoretic meanings.

The refinement U is indexed by all points of X, with c in U(c). A finite set s of these centers covers X. For each c in s there is one original member V(j) containing every selected U(d) that meets U(c). In particular, it contains the centers of those members. This is control of a whole star, rather than only control of each member separately.

Take a finite continuous partition of unity subordinate to V and put delta = 1 / (4 * (n + 1)). Let U(c) consist of points whose every partition coordinate differs from that of c by less than delta. These sets are open and centered. Compactness supplies the finite subcover.

At c, some coordinate is greater than three delta: otherwise the sum would be at most 3 * n / (4 * (n + 1)), which is less than one. If U(d) meets U(c), three coordinate differences control every point of U(d). That same coordinate stays positive, so subordination puts all of U(d) in V(j). No metric, dimension or local contractibility assumption on X is used.

This is a quantitative form of the classical partition-of-unity construction of star refinements. The exact finite construction is derived here from Mathlib's continuous partition of unity; it carries no originality claim. Convex averaging of fiber representatives uses the common original member to control all simultaneously active centers.

## References

- Truth anchor: `D5/S3/Topology/FiniteCenteredStarRefinement.exists_finite_centered_star_refinement`
