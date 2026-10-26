# Square roots on two full actual lift orbits

## Abstract

Two primitive base orbits can jointly admit an equivariant square root even when separate roots fail.

**Definition 1.1 (All original histories over both signed base orbits).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right),\; \operatorname{OrbitUnion}\left(C, P, Q\right) = \{x:\operatorname{History}\left(\operatorname{expandedGraph}\left(C\right)\right) \mid ((\exists t \in Int,\; \operatorname{forgetHistory}\left(x\right) = \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, P\right)) \lor (\exists t \in Int,\; \operatorname{forgetHistory}\left(x\right) = \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, Q\right)))\}$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.OrbitUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OrbitUnion C P Q is the subtype of every original bilateral legal history of expandedGraph C whose forgotten numbered-edge base history is translate(t,P) or translate(t,Q) for an integer t. The two alternatives retain all group coordinates and all original numbered edges. Neither a representative lift nor a selected subset of a fibre replaces this carrier.

**Definition 1.2 (The original time map restricted to the union).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right),\; \forall x \in \operatorname{OrbitUnion}\left(C, P, Q\right),\; \operatorname{value}\left(\operatorname{apply}\left(\operatorname{unionShift}\left(C, P, Q\right), x\right)\right) = \operatorname{shift}\left(\operatorname{expandedGraph}\left(C\right), \operatorname{value}\left(x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.unionShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

unionShift has exactly the original one-step history shift as its underlying value. Signed base orbit membership is invariant under this operation: a base translate by t becomes the translate by t+1.

**Definition 1.3 (The original left deck action restricted to the union).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right),\; \forall a \in H, x \in \operatorname{OrbitUnion}\left(C, P, Q\right),\; \operatorname{value}\left(\operatorname{unionDeck}\left(C, P, Q, a, x\right)\right) = \operatorname{groupHistory}\left(C, a, \operatorname{value}\left(x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.unionDeck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

unionDeck a acts by the original groupHistory C a. It leaves the forgotten base path, including every edge number, unchanged. The group is arbitrary and can be infinite or noncommutative.

**Theorem 1.4 (Complete square-root criterion).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right), d \in Nat, e \in Nat,\; ((((((\operatorname{Positive}\left(d\right)) \land (\operatorname{Positive}\left(e\right)))) \land (((((\operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), P\right) = d) \land (\operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), Q\right) = e))) \land (\forall t \in Int,\; \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, P\right) \neq Q))))) \implies (((\exists R \in \operatorname{Map}\left(\operatorname{OrbitUnion}\left(C, P, Q\right), \operatorname{OrbitUnion}\left(C, P, Q\right)\right),\; ((\forall a \in H, x \in \operatorname{OrbitUnion}\left(C, P, Q\right),\; \operatorname{apply}\left(R, \operatorname{unionDeck}\left(C, P, Q, a, x\right)\right) = \operatorname{unionDeck}\left(C, P, Q, a, \operatorname{apply}\left(R, x\right)\right)) \land (\operatorname{iterate}\left(R, 2\right) = \operatorname{unionShift}\left(C, P, Q\right)))) \iff (((((\exists s \in \operatorname{Fin}\left(d\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{orbitHolonomy}\left(C, P, d\right)\right)) \land (((\operatorname{mul}\left(2, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = (1+\operatorname{mul}\left(\operatorname{intCast}\left(d\right), m\right))) \land (\operatorname{mul}\left(b^{2}, \operatorname{orbitHolonomy}\left(C, P, d\right)^{m}\right) = 1))))) \land (\exists s \in \operatorname{Fin}\left(e\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{orbitHolonomy}\left(C, Q, e\right)\right)) \land (((\operatorname{mul}\left(2, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = (1+\operatorname{mul}\left(\operatorname{intCast}\left(e\right), m\right))) \land (\operatorname{mul}\left(b^{2}, \operatorname{orbitHolonomy}\left(C, Q, e\right)^{m}\right) = 1))))))) \lor (((d = e) \land (\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{orbitHolonomy}\left(C, Q, e\right)\right) = \operatorname{mul}\left(\operatorname{orbitHolonomy}\left(C, P, d\right), b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.square_root_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d and e be the positive minimal periods of P and Q, and suppose no signed translate of P equals Q. Put h=orbitHolonomy C P d and k=orbitHolonomy C Q e. An arbitrary deck-equivariant endomap R of the entire original-history union has R squared equal to the original shift exactly in the displayed two cases. The preserving case requires both signed local equations: there are s:Fin d, m:Int and b:H with Commute b h, 2*s.val=1+d*m and b^2*h^m=1, and independently the same conditions for Q,e,k. The exchanging case requires d=e and an intertwiner b*k=h*b. Holonomy order or equality of ordinary periodic counts cannot replace the displayed holonomy condition. No time-commutation, bijectivity or component-preservation premise is imposed on R.

For the reverse direction, the root equation first gives time commutation. Complete finite phase coordinates then show that the image tag of R is constant on each joint deck/time component. Applying the square equation to the two origins forces the tag map to be either the identity or the exchange. In the identity case the existing one-orbit root criterion gives the two local equations. In the exchange case each directed cross map carries the source seam into the target seam, giving d=e*m and e=d*n for integers m,n. Positivity forces d=e and m=n=1, so the first seam becomes b*k=h*b. This uses both directions of transport; equal infinite cardinalities would not determine the primitive periods.

For the converse exchange, complete atlas coordinates define F(point(t,z))=point(t,z*b) on the other component. Source equality at a signed seam m is respected because SemiconjBy.zpow_right directly gives b*k^m=h^m*b for every integer m. The inverse transport uses b inverse. Sending the first component through F and the second through time composed with F inverse squares to time on both. The complete charts are identified with the full original union by an equivalence whose underlying map is the same numbered-edge history; it intertwines original time and every original deck operation. Thus the construction neither omits histories nor adds artificial ones.

The argument combines classical permutation-centralizer component routing, regular-action right multiplication and ordered voltage-return holonomy. The one-orbit arithmetic is supplied by PrimitiveLiftRootCriterion; the signed power identity is supplied by pinned Mathlib SemiconjBy.zpow_right. This is a synthesis on actual history carriers and makes no claim of literature priority or global classification beyond these two signed base orbits.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.OrbitUnion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.square_root_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.unionDeck`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.unionShift`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion](PrimitiveLiftRootCriterion.md)
