# The global formula for interval-closed rowmotion

## Abstract

The interval-closed toggle sweep on a finite poset has an explicit formula in its initial ceiling and lower boundary.

Let P be an arbitrary partially ordered set. An equivalence e from Fin N to P enumerates all its points once, and a reverse extension visits every strictly larger point before every strictly smaller point. Start from an order-convex set I. The toggle at a point replaces the current state by its symmetric difference with that singleton exactly when the replacement is order-convex. The trace is the literal sequence of these toggles, with initial state I.

Theorem 1.1 and its proof in Lafreniere, Lewis, McNicholas, Striker and Welch, Interval-closed set rowmotion and homomesy on products of two chains, arXiv:2505.04000v1, give this finite-poset image formula. The ceiling, lower boundary and incomparable region below express the sets in that formula. The statement here uses an arbitrary universe and includes empty posets and empty boundaries.

The Lean proof adapts the set-side and local-flip arguments from Columbus Labs, interval-closed-rowmotion, as identified in the Lean source. That source retains the adaptation attribution and MIT license separately from the mathematical attribution to Lafreniere, Lewis, McNicholas, Striker and Welch.

**Definition 1.1 (The upper boundary).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall I \in Set(P),\; \forall x \in P,\; (x \in ceiling(I)) \Leftrightarrow (Minimal((upperClosure(I) \setminus I), x))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.ceiling` (`✓ std3`).

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

The ceiling C consists of the minimal elements of the upper closure of I outside I. All closures and minimality statements use the given partial order. The upper closure is non-strict, so it includes I itself.

**Definition 1.2 (The eligible initial minima).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall I \in Set(P),\; \forall x \in P,\; (x \in lowerBoundary(I)) \Leftrightarrow ((Minimal(I, x)) \land (x \in lowerClosure(ceiling(I))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.lowerBoundary` (`✓ std3`).

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

The lower boundary H is the intersection of the minimal elements of I with the lower closure of C. A minimum is eligible exactly when it lies below at least one ceiling point.

**Definition 1.3 (The full incomparable region).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall C \in Set(P),\; \forall x \in P,\; (x \in incomparable(C)) \Leftrightarrow (\forall c \in P,\; (c \in C) \Rightarrow ((\neg x \le c) \land (\neg c \le x)))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.incomparable` (`✓ std3`).

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

A point belongs to the incomparable region of C precisely when, for every c in C, neither the point is at most c nor c is at most the point. If C is empty, this region is the whole poset.

**Definition 1.4 (The proposed image).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall I \in Set(P),\; formula(I) = (incomparable(ceiling(I)) \setminus I) \cup (lowerClosure(ceiling(I)) \setminus lowerClosure(lowerBoundary(I)))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.formula` (`✓ std3`).

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

Take the union of the incomparable region outside I and the lower closure of C outside the lower closure of H. Both differences are ordinary set differences. The expression depends only on I and the order, and does not use a toggle trace.

**Theorem 1.5 (Every reverse extension gives the explicit image).**

$$\forall P \in \mathrm{Type},\; [PartialOrder(P)] \forall N \in \mathrm{Nat},\; \forall e \in Equiv(Fin(N), P),\; \forall I \in Set(P),\; (ReverseExtension(e)) \Rightarrow ((OrdConnected(I)) \Rightarrow (trace(e, I, N) = formula(I)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.trace_eq_formula` (`✓ std3`). ∎

*Citation.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

For every natural N, every equivalence e from Fin N to P satisfying the reverse-extension condition, and every order-convex initial I, the final literal state trace(e,I,N) equals formula(I). There are no nonemptiness assumptions on P, I, C or H, and the theorem includes N=0.

The ceiling is an antichain. Finiteness supplies a minimal initial hole below every point of the upper closure outside I. Conversely, order-convexity shows that every point above a ceiling point is outside I. Thus the upper closure of C is exactly the upper closure of I outside I. The lower and upper closures of the antichain meet precisely in C.

The proposed image is order-convex. No point in it lies below an eligible initial minimum. Between two proposed-image points, a point in the lower closure of C therefore belongs to the second difference. A point outside that lower closure has no ceiling point below it, because the larger endpoint lies in the incomparable region. It also cannot belong to I: otherwise the larger endpoint would be above an initial point but outside I, and hence above a ceiling point. This puts it in the first difference.

Every ceiling point belongs to the proposed image, and every minimal point of I is excluded. A point initially in I belongs to the proposed image exactly when an initially included point lies strictly below it and a proposed-image point lies strictly above it. For an initially absent point, membership is equivalent to two no-hole conditions: all intervals up from initially included lower endpoints are filled in I below the point, and all intervals down from proposed-image upper endpoints are filled in the proposed image above the point.

To connect these conditions to the actual dynamics, consider an order-convex intermediate state at the visit of x. Suppose its membership agrees with I at x and strictly below x, and with the proposed image strictly above x. If x is initially present, deletion fails exactly when two retained endpoints force x to remain between them. If x is initially absent, insertion is legal exactly when both no-hole conditions hold. Consequently, toggling x makes its membership equal to the proposed image. Membership at every other point stays fixed.

Induction over the enumeration now shows that processed points have their proposed-image membership and unprocessed points have their initial membership. Reverse order ensures the lower and upper agreements needed at each visit. Each literal toggle preserves order-convexity by its definition. At N every point has been processed, giving the asserted equality. For an empty ceiling the formula reduces to the complement of I; for an empty poset the same induction has no visits. Neither case requires a separate existence assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.ceiling`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.formula`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.incomparable`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.lowerBoundary`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula.trace_eq_formula`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport](RowmotionEndpointTransport.md)
