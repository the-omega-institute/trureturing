# Cube roots on three signed return charts

## Abstract

Three complete return charts admit an equivariant cube root exactly by local roots or a compatible component cycle.

**Definition 1.1 (Time on the three-chart carrier).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, Z \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), C \in \operatorname{ReturnAtlas}\left(H, Z\right),\; \operatorname{jointTime}\left(A, B, C\right) = \operatorname{sumMap}\left(\operatorname{time}\left(A\right), \operatorname{sumMap}\left(\operatorname{time}\left(B\right), \operatorname{time}\left(C\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.jointTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is X plus (Y plus Z), with no identification across components. jointTime applies each chart's specified time map to its own component.

**Definition 1.2 (The joint left deck action).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, Z \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), C \in \operatorname{ReturnAtlas}\left(H, Z\right),\; \forall a \in H, x \in \operatorname{Sum}\left(X, \operatorname{Sum}\left(Y, Z\right)\right),\; \operatorname{jointDeck}\left(A, B, C, a, x\right) = \operatorname{apply}\left(\operatorname{sumMap}\left(\operatorname{deck}\left(A, a\right), \operatorname{sumMap}\left(\operatorname{deck}\left(B, a\right), \operatorname{deck}\left(C, a\right)\right)\right), x\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.jointDeck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each group element acts by the given left deck map on every chart. The group may be infinite or noncommutative.

**Definition 1.3 (The signed one-chart cube-root equation).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right),\; ((\operatorname{Local}\left(A\right)) \iff (\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(A\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(A\right)\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{holonomy}\left(A\right)^{m}\right) = 1))))))$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.Local` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Local A means that some finite phase s, signed return exponent m and group element b satisfy Commute b h, 3*s.val=1+d*m and b^3*h^m=1, where d=A.period and h=A.holonomy. The return exponent can be negative.

**Theorem 1.4 (Complete equivariant cube-root criterion).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall X \in Type, Y \in Type, Z \in Type, A \in \operatorname{ReturnAtlas}\left(H, X\right), B \in \operatorname{ReturnAtlas}\left(H, Y\right), C \in \operatorname{ReturnAtlas}\left(H, Z\right),\; ((\exists r \in \operatorname{Map}\left(\operatorname{Sum}\left(X, \operatorname{Sum}\left(Y, Z\right)\right), \operatorname{Sum}\left(X, \operatorname{Sum}\left(Y, Z\right)\right)\right),\; ((\forall a \in H, x \in \operatorname{Sum}\left(X, \operatorname{Sum}\left(Y, Z\right)\right),\; \operatorname{apply}\left(r, \operatorname{jointDeck}\left(A, B, C, a, x\right)\right) = \operatorname{jointDeck}\left(A, B, C, a, \operatorname{apply}\left(r, x\right)\right)) \land (\operatorname{iterate}\left(r, 3\right) = \operatorname{jointTime}\left(A, B, C\right)))) \iff (((((\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(A\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(A\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(A\right)\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{holonomy}\left(A\right)^{m}\right) = 1))))) \land (((\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(B\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(B\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(B\right)\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{holonomy}\left(B\right)^{m}\right) = 1))))) \land (\exists s \in \operatorname{Fin}\left(\operatorname{period}\left(C\right)\right), m \in Int, b \in H,\; ((\operatorname{Commute}\left(b, \operatorname{holonomy}\left(C\right)\right)) \land (((\operatorname{mul}\left(3, \operatorname{intCast}\left(\operatorname{val}\left(s\right)\right)\right) = 1+\operatorname{mul}\left(\operatorname{intCast}\left(\operatorname{period}\left(C\right)\right), m\right)) \land (\operatorname{mul}\left(b^{3}, \operatorname{holonomy}\left(C\right)^{m}\right) = 1))))))))) \lor (((\operatorname{period}\left(A\right) = \operatorname{period}\left(B\right)) \land (((\operatorname{period}\left(B\right) = \operatorname{period}\left(C\right)) \land (((\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{holonomy}\left(B\right)\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(A\right), b\right)) \land (\exists b \in H,\; \operatorname{mul}\left(b, \operatorname{holonomy}\left(C\right)\right) = \operatorname{mul}\left(\operatorname{holonomy}\left(B\right), b\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.chart_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A deck-equivariant endomap has cube equal to jointTime precisely when each chart satisfies its local signed equation, or all three periods agree and consecutive holonomies admit the displayed intertwiners. The root is not assumed to commute with time, to be bijective or to preserve components. A return atlas already includes a positive period and a complete equality law.

The root equation implies time commutation. Finite phase coordinates and deck equivariance force the target component to be constant on each source component. The resulting map of three labels has cube equal to the identity, so it is the identity or one of the two three-cycles. In a three-cycle, the three directed seam equations give cyclic divisibility of the positive periods. All divisibility multipliers must therefore equal one, and the seam equations become holonomy intertwiners.

Conversely, local roots act separately. For compatible holonomies, transport in signed coordinates sends point(t,z) to point(t,z*b) on the next chart. Two successive transports use b and c. The return arrow uses (b*c) inverse and then one time step. The resulting map cubes to time on every component; the order of the factors is essential for a noncommutative group. This is a structural consequence of complete return charts and classical permutation component routing, without a claim of literature priority.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.Local`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.chart_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.jointDeck`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.jointTime`
- Dependency: [D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion](TwoOrbitSquareRootCriterion.md)
