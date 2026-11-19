# Convex averaging with whole-fiber control

## Abstract

Finite convex averaging gives a continuous map avoiding a forbidden set while controlling every point of every fiber.

**Theorem 1.1 (A continuous average without continuous fiber selections).**

$$\forall X \in Types,\; \forall E \in Types,\; [TopologicalSpace\left(X\right)] [CompactSpace\left(X\right)] [TTwoSpace\left(X\right)] [NormedAddCommGroup\left(E\right)] [NormedSpace\left(Real, E\right)] \forall n \in Nat,\; \forall V \in Fin\left(n\right) \to Set\left(X\right),\; \forall B \in X \to Set\left(E\right),\; \forall N \in Fin\left(n\right) \to Set\left(E\right),\; \forall K \in Set\left(E\right),\; \forall L \in Set\left(E\right),\; \forall R \in Set\left(E\right),\; \forall O \in Set\left(X\right),\; \forall a \in X \to E,\; \left(\left(\forall j \in Fin\left(n\right),\; IsOpen\left(V\left(j\right)\right)\right) \land \left(\left(\forall x \in X,\; \exists j \in Fin\left(n\right),\; x \in V\left(j\right)\right) \land \left(Convex\left(Real, K\right) \land \left(Convex\left(Real, L\right) \land \left(\left(\forall j \in Fin\left(n\right),\; Convex\left(Real, N\left(j\right)\right)\right) \land \left(\left(\forall x \in X,\; Subset\left(B\left(x\right), K\right)\right) \land \left(\left(\forall j \in Fin\left(n\right),\; \forall x \in X,\; x \in V\left(j\right) \Rightarrow Subset\left(B\left(x\right), N\left(j\right)\right)\right) \land \left(\left(\forall j \in Fin\left(n\right),\; \neg {0 \in N\left(j\right)}\right) \land \left(\left(\forall j \in Fin\left(n\right),\; Disjoint\left(N\left(j\right), R\right) \lor Subset\left(V\left(j\right), O\right)\right) \land \left(Subset\left(Inter\left(L, R\right), Singleton\left(0\right)\right) \land \left(\left(\forall x \in X,\; a\left(x\right) \in B\left(x\right)\right) \land \left(\forall x \in X,\; x \in O \Rightarrow a\left(x\right) \in L\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists A \in ContinuousMaps\left(X, E\right),\; \left(\forall x \in X,\; A\left(x\right) \in K\right) \land \left(\left(\forall x \in X,\; \neg {A\left(x\right) \in R}\right) \land \left(\forall x \in X,\; \forall b \in E,\; b \in B\left(x\right) \Rightarrow \neg {0 \in segment\left(Real, b, A\left(x\right)\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is any compact Hausdorff space and E any real normed vector space. V is a finite open cover. B(x) is a subset of E for each x; the notation fiber imposes no additional regularity assumption. Every B(x) lies in the convex set K. Each V(j) controls its entire fiber: x in V(j) implies B(x) is contained in the convex set N(j), and zero is outside every N(j).

R is the forbidden subset of E. It need not itself be a ray for this construction. For each j, either N(j) is disjoint from R, or V(j) lies in O. The convex slice L meets R only possibly at zero. The arbitrary representatives a(x) belong to B(x), and belong to L whenever x lies in O. They are not assumed continuous. ContinuousMaps denotes continuous maps, Inter denotes intersection, Singleton denotes a singleton, Subset denotes inclusion, and segment denotes the closed affine segment.

Construct a finite centered star refinement and take a second partition of unity subordinate to it. Average the finitely many representatives at its centers. The weights are continuous, nonnegative and sum to one, so this average A is continuous and lies in K.

At any x choose a refinement member with positive weight. Every other active member meets it at x. The star condition puts x and all active centers in one V(j). Thus B(x) and every active representative lie in the same N(j), and convexity puts A(x) there too. Every segment from any b in B(x) to A(x) stays in N(j), so it avoids zero.

If that N(j) is disjoint from R, the average avoids R. Otherwise every active center is in O, so every active representative lies in L and the average lies in L. Membership in R would force A(x) to be zero, contradicting its membership in N(j). This checks the mixed terms through a common convex set; separate bounds on individual representatives would not suffice.

The result supplies a finite convex construction, with no dimension, metrizability or continuous-selection assumption on X and no finite-dimensional assumption on E. Applying it to a boundary quotient still requires construction of the quotient, a common slice, the finite controlling neighborhoods and the stated representatives. Radial projection and the final topological obstruction are further conclusions, not hypotheses or conclusions of this theorem. The construction carries no originality claim.

## References

- Truth anchor: `D5/S3/Topology/FiniteConvexFiberMap.exists_continuous_ray_avoiding_fiber_map`
- Dependency: [D5/S3/Topology/FiniteCenteredStarRefinement](FiniteCenteredStarRefinement.md)
