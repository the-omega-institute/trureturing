# Equivariant cube roots on three primitive lift orbits

## Abstract

The complete original histories over three disjoint primitive base orbits admit precisely local cube roots or a compatible three-cycle.

**Definition 1.1 (All original histories over the three signed base orbits).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right), S \in \operatorname{Path}\left(C\right),\; \operatorname{OrbitUnion}\left(C, P, Q, S\right) = \{x:\operatorname{History}\left(\operatorname{expandedGraph}\left(C\right)\right) \mid ((\exists t \in Int,\; \operatorname{forgetHistory}\left(x\right) = \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, P\right)) \lor (((\exists t \in Int,\; \operatorname{forgetHistory}\left(x\right) = \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, Q\right)) \lor (\exists t \in Int,\; \operatorname{forgetHistory}\left(x\right) = \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, S\right)))))\}$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.OrbitUnion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OrbitUnion C P Q S contains every original bilateral legal history of expandedGraph C whose forgotten numbered-edge history is an integer translate of P, Q or S. All phases and group coordinates remain present.

**Definition 1.2 (The restricted original time shift).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right), S \in \operatorname{Path}\left(C\right),\; \forall x \in \operatorname{OrbitUnion}\left(C, P, Q, S\right),\; \operatorname{value}\left(\operatorname{apply}\left(\operatorname{unionShift}\left(C, P, Q, S\right), x\right)\right) = \operatorname{shift}\left(\operatorname{expandedGraph}\left(C\right), \operatorname{value}\left(x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.unionShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The time map is exactly the original one-step shift on each underlying history. An integer base phase t becomes t+1.

**Definition 1.3 (The original deck action on the full union).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right), S \in \operatorname{Path}\left(C\right),\; \forall a \in H, x \in \operatorname{OrbitUnion}\left(C, P, Q, S\right),\; \operatorname{value}\left(\operatorname{unionDeck}\left(C, P, Q, S, a, x\right)\right) = \operatorname{groupHistory}\left(C, a, \operatorname{value}\left(x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.unionDeck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left action of a is the original groupHistory C a. It preserves the forgotten numbered-edge history. No finiteness or commutativity assumption is imposed on H.

**Theorem 1.4 (Complete three-orbit cube-root criterion).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), P \in \operatorname{Path}\left(C\right), Q \in \operatorname{Path}\left(C\right), S \in \operatorname{Path}\left(C\right), d \in Nat, e \in Nat, f \in Nat,\; ((((((\operatorname{Positive}\left(d\right)) \land (((\operatorname{Positive}\left(e\right)) \land (\operatorname{Positive}\left(f\right)))))) \land (((((\operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), P\right) = d) \land (((\operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), Q\right) = e) \land (\operatorname{minimalPeriod}\left(\operatorname{baseShift}\left(C\right), S\right) = f))))) \land (((\forall t \in Int,\; \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, P\right) \neq Q) \land (((\forall t \in Int,\; \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, P\right) \neq S) \land (\forall t \in Int,\; \operatorname{translate}\left(\operatorname{baseGraph}\left(C\right), t, Q\right) \neq S))))))))) \implies (((\exists R \in \operatorname{Map}\left(\operatorname{OrbitUnion}\left(C, P, Q, S\right), \operatorname{OrbitUnion}\left(C, P, Q, S\right)\right),\; ((\forall a \in H, x \in \operatorname{OrbitUnion}\left(C, P, Q, S\right),\; \operatorname{apply}\left(R, \operatorname{unionDeck}\left(C, P, Q, S, a, x\right)\right) = \operatorname{unionDeck}\left(C, P, Q, S, a, \operatorname{apply}\left(R, x\right)\right)) \land (\operatorname{iterate}\left(R, 3\right) = \operatorname{unionShift}\left(C, P, Q, S\right)))) \iff (((((\exists s \in \operatorname{Fin}\left(d\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{orbitHolonomy}\left(C, P, d\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(d\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{orbitHolonomy}\left(C, P, d\right)^{m}\right) = 1))))) \land (((\exists s \in \operatorname{Fin}\left(e\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{orbitHolonomy}\left(C, Q, e\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(e\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{orbitHolonomy}\left(C, Q, e\right)^{m}\right) = 1))))) \land (\exists s \in \operatorname{Fin}\left(f\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{orbitHolonomy}\left(C, S, f\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(f\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{orbitHolonomy}\left(C, S, f\right)^{m}\right) = 1))))))))) \lor (((d = e) \land (((e = f) \land (((\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{orbitHolonomy}\left(C, Q, e\right)\right) = \operatorname{mul}\left(\operatorname{orbitHolonomy}\left(C, P, d\right), b\right)) \land (\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{orbitHolonomy}\left(C, S, f\right)\right) = \operatorname{mul}\left(\operatorname{orbitHolonomy}\left(C, Q, e\right), b\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.cube_root_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d,e,f be the positive minimal periods of P,Q,S, whose signed base orbits are pairwise disjoint. A deck-equivariant endomap R of the entire original-history union cubes to the original shift exactly when the three local signed cube-root equations all hold, or d=e=f and consecutive ordered holonomies admit intertwiners b*hQ=hP*b and c*hS=hQ*c. Each local equation has s:Fin d, m:Int and b:H with Commute b h, 3*s.val=1+d*m and b^3*h^m=1, and independently for the other components. No preservation of components, time commutation or bijectivity is assumed of R.

The three signed base-orbit hypotheses identify the disjoint union of the complete actual lift atlases with this full history subtype. The equivalence keeps the very same underlying numbered-edge history, intertwines every original deck operation and intertwines the original time shift. Conjugating an arbitrary root through it gives precisely the three-chart cube-root problem, rather than a root on selected representatives or a reduced fibre.

The atlas criterion extracts the induced action on three components. A cube root either preserves them all or permutes them in a three-cycle. In the latter case cyclic seam divisibility forces the three primitive periods to be equal, and the ordered seam equations force the displayed conjugacies. Compatible transports then construct a root with one time step on the closing arrow. The order in these group equations is retained; equal holonomy orders or equal ordinary periodic counts are insufficient substitutes. The result concerns these three signed base orbits and does not claim a classification for an arbitrary number of components or literature priority.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.OrbitUnion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.cube_root_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.unionDeck`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.unionShift`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts](ThreeOrbitCubeRootCharts.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion](TwoOrbitSquareRootCriterion.md)
