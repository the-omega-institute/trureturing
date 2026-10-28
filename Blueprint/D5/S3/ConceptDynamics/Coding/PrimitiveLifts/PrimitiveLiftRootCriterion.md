# Equivariant roots on actual primitive lifts

## Abstract

A primitive base orbit retains an ordered group return invisible to ordinary periodic counts.

**Definition 1.1 (Complete signed return charts).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type,\; \operatorname{ReturnAtlas}\left(H, X\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.ReturnAtlas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReturnAtlas H X contains d>0, g:H, a surjective point:Int->H->X, time and the left deck action. Its exact equality law is point(t,z)=point(s,w) iff there is an integer m with t=s+d*m and z*g^m=w. The time and deck laws are time(point(t,z))=point(t+1,z) and deck(a,point(t,z))=point(t,a*z). No commutativity or finiteness assumption on H is imposed by this structure. The signed relation is a complete equality criterion, rather than an assumed classification of equivariant maps.

**Definition 1.2 (All phases and all group coordinates).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; \operatorname{Equiv}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), H\right), X\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence sends (q,z) to point(q.val,z), with q in Fin d. Injectivity uses the exact return relation and the strict phase bounds. Surjectivity reduces any integer t by Euclidean division, replacing z with z*g^(t/d). This includes negative times and every group coordinate.

**Theorem 1.3 (Time is injective).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; \operatorname{Injective}\left(\operatorname{time}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.time_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the time images of point(t,z) and point(s,w) gives t+1=s+1+d*m and z*g^m=w. Cancelling the added step recovers the original signed equality. Therefore the specified time map is injective on the full chart carrier.

**Definition 1.4 (The specified left deck action).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; \forall f \in \operatorname{Map}\left(X, X\right),\; \operatorname{Equivariant}\left(A, f\right) = \left(\forall a \in H, x \in X,\; \operatorname{apply}\left(f, \operatorname{deck}\left(A, a, x\right)\right) = \operatorname{deck}\left(A, a, \operatorname{apply}\left(f, x\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.Equivariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equivariance always uses multiplication on the left. The holonomy seam acts on the right; these two operations are kept distinct for nonabelian groups.

**Theorem 1.5 (Unique reverse classification).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), f \in \operatorname{Map}\left(X, X\right),\; (((\operatorname{Equivariant}\left(A, f\right) \land \operatorname{FunctionCommute}\left(f, \operatorname{time}\left(A\right)\right))) \implies (\exists q \in \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), H\right),\; ((\operatorname{Commute}\left(\operatorname{second}\left(q\right), \operatorname{holonomy}\left(A\right)\right) \land \forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(A, (t+\operatorname{val}\left(\operatorname{first}\left(q\right)\right)), \operatorname{mul}\left(z, \operatorname{second}\left(q\right)\right)\right)) \land \forall r \in \operatorname{Prod}\left(\operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), H\right),\; (((\operatorname{Commute}\left(\operatorname{second}\left(r\right), \operatorname{holonomy}\left(A\right)\right) \land \forall t \in Int, z \in H,\; \operatorname{apply}\left(f, \operatorname{point}\left(A, t, z\right)\right) = \operatorname{point}\left(A, (t+\operatorname{val}\left(\operatorname{first}\left(r\right)\right)), \operatorname{mul}\left(z, \operatorname{second}\left(r\right)\right)\right))) \implies (r = q)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every deck-equivariant f commuting with time there is exactly one q=(s,b) in Fin d times H such that b commutes with g and f(point(t,z))=point(t+s,z*b) for every signed t and z. Read f(point(0,1)) in the complete coordinates. Equivariance and time commutation propagate this image in both time directions; time injectivity is derived from the return relation. Comparing the two images of point(d,1)=point(0,g) forces b*g=g*b. Finally the image of point(0,1) proves uniqueness. In the finite phase coordinates this is T^s composed with the right map R_b.

**Definition 1.6 (Constructed maps on the same carrier).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; \forall s \in Int, b \in H, x \in X,\; \operatorname{normalMap}\left(A, s, b, x\right) = \operatorname{point}\left(A, (\operatorname{val}\left(\operatorname{first}\left(\operatorname{inverseCoordinates}\left(A, x\right)\right)\right)+s), \operatorname{mul}\left(\operatorname{second}\left(\operatorname{inverseCoordinates}\left(A, x\right)\right), b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normalMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the existing carrier X and its complete coordinate equivalence. When b commutes with g, its value on every signed coordinate is point(t+s,z*b); the seam constraint proves independence of the chosen representative. Iteration gives point(t+k*s,z*b^k), which is used in the root construction.

**Definition 1.7 (Lawful normal maps are permutations).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; \forall s \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(A\right)\right)) \implies (\operatorname{normalEquiv}\left(A, s, b\right):\operatorname{Perm}\left(X\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalEquiv(s,b) has normalMap(s,b) as its forward function and normalMap(-s,inverse(b)) as its inverse. The complete signed-coordinate law proves both inverse identities. Thus the normal form also implies that every deck-equivariant map commuting with time is bijective. The root criterion constructs its sufficient witness using this permutation.

**Theorem 1.8 (Exact root equation with a signed seam exponent).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), k \in Nat,\; ((\exists f \in \operatorname{Map}\left(X, X\right),\; (\operatorname{Equivariant}\left(A, f\right) \land \operatorname{iterate}\left(f, k\right) = \operatorname{time}\left(A\right))) \iff (\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), m \in Int, b \in H,\; (\operatorname{Commute}\left(b, \operatorname{holonomy}\left(A\right)\right) \land (\operatorname{mul}\left(k, \operatorname{val}\left(s\right)\right) = (1+\operatorname{mul}\left(\operatorname{period}\left(A\right), m\right)) \land \operatorname{mul}\left(b^{k}, \operatorname{holonomy}\left(A\right)^{m}\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.root_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural k, a deck-equivariant f with f iterated k times equal to time exists exactly when there are s:Fin d, m:Int and b:H with b*g=g*b, k*s.val=1+d*m and b^k*g^m=1. In particular this gives every positive root order requested. The root equation implies time commutation, so no such premise is added to root existence. The necessity uses the reverse normal form and then the exact return relation. The sufficiency constructs normalMap(s.val,b) on X and checks its kth iterate on every coordinate. At d=1 the canonical phase is zero and m=-1, giving b^k=g. Restricting m to natural numbers would lose precisely this case.

**Definition 1.9 (Actual ordered loop label).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), p \in \operatorname{Path}\left(C\right), d \in Nat,\; \operatorname{orbitHolonomy}\left(C, p, d\right) = \operatorname{totalLabel}\left(\operatorname{historyWindow}\left(\operatorname{baseGraph}\left(C\right), p, 0, d\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.orbitHolonomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The loop retains the original numbered edges and their time order. For d equal to the minimal positive base period its endpoints agree. Its total label equals the coordinate at time d of anchoredHistory(p,1), proved by comparing prefixLabel with the existing ordered positiveLabels list.

**Definition 1.10 (Every lift of one specified base orbit).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), p \in \operatorname{Path}\left(C\right), d \in Nat,\; \operatorname{LiftOrbit}\left(C, p, d\right) = \operatorname{Subtype}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(C\right)\right), \operatorname{liesOverForwardPhase}\left(C, p, d\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.LiftOrbit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LiftOrbit C p d consists exactly of actual History(expandedGraph C) whose forgetHistory equals the qth base shift of p for some q:Fin d. liesOverForwardPhase denotes this existential predicate. No history is discarded inside a fibre. The construction is local to this base orbit; a global map on several base orbits can permute them.

**Definition 1.11 (Actual histories realize the complete return relation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), p \in \operatorname{Path}\left(C\right), d \in Nat,\; (((\operatorname{Positive}\left(d\right) \land \operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), p\right) = d)) \implies (\operatorname{ReturnAtlas}\left(H, \operatorname{LiftOrbit}\left(C, p, d\right)\right)))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.actualAtlas` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructed atlas has period d, holonomy equal to the actual loop label, time equal to the restricted original one-step shift, and deck equal to groupHistory. Its point(t,z) is groupHistory(z,translate(t,anchoredHistory(p,1))). The existing anchoredEquiv proves that all actual lifts are covered. The existing signed_recovery theorem supplies the full positive and negative return law. Euclidean reduction and mathlib's injectivity of iterates below the minimal period separate phases. Comparing the remaining group coordinates yields the exact relation point(t,z)=point(s,w) iff t=s+d*m and z*g^m=w. Thus the reverse classification and root criterion apply to this actual history subsystem, with no separately assumed finite model. The actual bridge, like the abstract return argument, requires neither finiteness nor commutativity of H. This is a repository synthesis of the classical ordered voltage-return and regular-action mechanisms; no claim of new mathematics in the literature is made.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.Equivariant`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.LiftOrbit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.ReturnAtlas`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.actualAtlas`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.coordinates`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normalEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normalMap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.normal_form`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.orbitHolonomy`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.root_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.time_injective`
- Dependency: [D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories](../OrderedGroupChainHistories.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/TwistedPeriodicHistories](../TwistedPeriodicHistories.md)
