# Cut-independent coordinates of actual beams

## Abstract

Cut-independent coordinates of actual beams.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Select a cut only to define an intrinsic coordinate).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right),\; \forall U \in \operatorname{Beam}\left(G\right),\; \operatorname{hasType}\left(\operatorname{beamCoordinate}\left(G, U\right), \operatorname{RowLimit}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates.beamCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RowLimit G is the existing StationaryModule of rowTransition G = (adjacency G).toLinearMapRight'. hasType displays a definition's result type, not a new proposition. coordinateAt G U n hn is intStage (rowTransition G) n (endpointRow G U n), installing hn.1 as the finite-parts instance. beamCoordinate uses a cut chosen from U.property. With Essential G, coordinateAt_eq removes dependence on that choice and coordinateAt_ray gives intStage n (Pi.single (endpoint alpha n) 1).

**Theorem 1.2 (Two cuts of the same actual beam give the same integer class).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \forall U \in \operatorname{Set}\left(\operatorname{History}\left(G\right)\right), n \in Int, m \in Int, hn \in \operatorname{AtCut}\left(G, U, n\right), hm \in \operatorname{AtCut}\left(G, U, m\right),\; \operatorname{coordinateAt}\left(G, U, n, hn\right) = \operatorname{coordinateAt}\left(G, U, m, hm\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates.coordinateAt_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both intrinsic partitions refine to max n m, with natural lengths (max n m-n).toNat and (max n m-m).toNat. endpointRow_refine and intStage_refine identify their coordinates. Negative cuts and equal ray sets arising from unique continuation remain in scope; no cut is identified by an inverse transition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates.beamCoordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates.coordinateAt_eq`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts](StandardBeamColimitCuts.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows](StandardBeamEndpointRows.md)
