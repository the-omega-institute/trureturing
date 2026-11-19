# DendriteObstruction - MinimalInvariant

## Abstract

The continuum-preserving minimal-set and tail-orbit obstruction without uniform arc packing.

**Theorem 1.1 (Minimal invariant compactum retaining a continuum).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_minimal_invariant_continuum`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_minimal_invariant_continuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a finitely positively expansive continuous self-map of a compact metric space with StaticArcHull and an actual nondegenerate embedded arc. There exists an inclusion-minimal compact forward-invariant set Y containing a nondegenerate compact connected subset. Y itself may be disconnected.

For a Bowen radius epsilon, take a=epsilon/4. The accepted continuum_expands proof makes the actual NonemptyCompacts family of continua inside each admissible Y with diameter at least a nonempty. It is compact by compact_continua_ge_in. Along any nonempty inclusion chain these families are directed under reverse inclusion; compact intersection retains a continuum of diameter at least a in the intersection of the original sets. That intersection is compact and forward invariant. The empty chain has the explicit bound X. Zorn minimizes exactly the class InvariantContinuumSet, rather than all nonempty invariant compacta.

**Theorem 1.2 (The least continuum containing a disconnected set).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_least_continuum`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_least_continuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a compact metric space with StaticArcHull, every nonempty subset Y has a least containing compact connected set H. Choose y0 in Y, take the union of the actual joining arcs from y0 to each other y in Y, use the singleton at y0, and take closure. The union is preconnected because every constituent contains y0. Static arc containment makes the closure lie in every subcontinuum containing Y. Neither Y nor this hull is assumed forward invariant.

**Theorem 1.3 (The complete dynamic contradiction under the classical static premise).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_of_coconnected_openings`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_of_coconnected_openings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be compact metric, contain an embedded nondegenerate arc, and satisfy StaticArcHull, the no-circle law, and SmallCoconnectedOpenings. Then every continuous self-map fails FinitelyPositiveExpansive. The opening law says that every nondegenerate subcontinuum H has a compact connected subset Q contained in H whose nonempty relative complement has arbitrarily small diameter. Since Q is closed, the complement is relatively open. No uniform arc-packing assumption occurs.

Minimize a compact forward-invariant Y among those containing a nondegenerate continuum and obtain an actual arc K in Y on which all iterates are injective, using the source-restricted accepted compact-history proof. Form its least continuum hull H. The accepted eventual_arc_persistence gives a common positive scale delta. A co-connected opening H minus Q of diameter below delta must meet Y; otherwise Q would contradict the leastness of H.

Split K into consecutive closed thirds L,M,R. At every sufficiently late time, each end third has diameter at least delta and therefore meets Q. Parameter order and injectivity on the whole K give an actual arc between those two outside points containing the entire image of M. Static arc convexity places that middle image in Q. The closure Z of the union of all these late middle images is compact and forward invariant, lies in Y intersect Q, and contains the actual nondegenerate continuum f^[T](M). It is a proper subset of Y, contradicting exactly the chosen minimality.

This module's static-to-dynamic theorem retains its explicit opening premise. AllDendroid separately proves that the opening law follows from the standard compact metric dendroid definition, using ProperExpansion, CoconnectedOpening and TentObstruction, and consumes it to establish the all-dendroid conclusion. Heath and Nall, Centers of a dendroid, Fundamenta Mathematicae 189, pages 173-183, DOI 10.4064/fm189-2-6, state on page 180 that every dendroid has endpoints in arbitrarily small co-connected open sets. The corresponding Krasinkiewicz-Minc result is classical; its static argument is formalized in those separate modules without a new Lean axiom. The full one-dimensional GGO classification question remains outside this class obstruction.

**Theorem 1.4 (Exact strict finite-set conclusion).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_iff_finite_small_orbits`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_iff_finite_small_orbits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every self-map of any metric space, failure of FinitelyPositiveExpansive is equivalent to the following statement: for every epsilon>0 and every natural m>=2 there is a finite set of exactly m distinct points whose joint iterated image diameter is strictly below epsilon at every natural time, including zero. No continuity or compactness is required for this equivalence.

In the forward direction, failure of the cardinal bound at radius epsilon/3 supplies an actual injection from Fin m into a single forward Bowen set. The finite image has cardinal m, and the triangle inequality bounds each image diameter by 2epsilon/3. Conversely an (N+1)-point set with the strict joint diameter bound lies in the radius-epsilon forward Bowen set of any of its points and contradicts cardinal bound N.

**Theorem 1.5 (Original finite-set quantifiers with the static premise explicit).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.finite_small_orbits_of_standard_dendroid_and_openings`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.finite_small_orbits_of_standard_dendroid_and_openings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every nondegenerate compact metric StandardDendroid satisfying the separately stated SmallCoconnectedOpenings law, every continuous self-map has, for every epsilon>0 and every m>=2, exactly m distinct points with joint iterated image diameter below epsilon for every natural time. The standard carrier supplies StaticArcHull and no_circle; the complete dynamic contradiction and the exact finite-set equivalence give the conclusion.

The sole additional static hypothesis is visible in this compiled conditional theorem. It is not included in StandardDendroid. AllDendroid proves that hypothesis separately through ProperExpansion, CoconnectedOpening and TentObstruction, then consumes this theorem to obtain the original all-standard-dendroid finite-set conclusion.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_least_continuum`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.exists_minimal_invariant_continuum`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.finite_small_orbits_of_standard_dendroid_and_openings`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_iff_finite_small_orbits`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/MinimalInvariant.not_finitelyPositiveExpansive_of_coconnected_openings`
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories](CompactHistories.md)
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid](StandardDendroid.md)
