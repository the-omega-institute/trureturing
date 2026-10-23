# Actual integer-cut rays and intrinsic finite beams

## Abstract

Actual integer-cut rays and intrinsic finite beams.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (The whole fixed past at any integer cut).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \forall alpha \in \operatorname{History}\left(G\right), n \in Int, x \in \operatorname{History}\left(G\right),\; x \in \operatorname{ray}\left(G, alpha, n\right) \Leftrightarrow \left(\forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(x, k\right) = \operatorname{coordinate}\left(alpha, k\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.ray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ray G alpha n is the actual subset fixing every edge k<=n, including arbitrarily negative k. Its endpoint is G.target(alpha n). Rays at a fixed cut are disjoint or equal as sets. RayAt stores those actual sets, so equality removes a repeated past rather than merely a repeated endpoint.

**Definition 1.2 (Replace an entire past and keep every future edge).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \forall alpha \in \operatorname{History}\left(G\right), beta \in \operatorname{History}\left(G\right), n \in Int, ep \in \operatorname{endpoint}\left(G, alpha, n\right) = \operatorname{endpoint}\left(G, beta, n\right),\; \operatorname{Equiv}\left(\operatorname{ray}\left(G, alpha, n\right), \operatorname{ray}\left(G, beta, n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.spliceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equiv denotes Lean Equiv between the two ray subtypes. spliceEquiv uses beta k for k<=n and the supplied ray member x k for k>n. Equality of the two target endpoints is precisely the seam hypothesis. Replacing the past back proves both inverse identities; no future is selected or restricted.

**Theorem 1.3 (All numbered continuations partition the full ray).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \forall alpha \in \operatorname{History}\left(G\right), n \in Int, r \in Nat,\; \operatorname{ray}\left(G, alpha, n\right) = \operatorname{refinedRayUnion}\left(G, hG, alpha, n, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.ray_refine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

refinedRayUnion is the indexed union over p : Continuation G (endpoint G alpha n) r of ray G (refined G hG alpha n r p) (n+(r:Int)). Continuation is PUnit at length zero and a dependent pair of an actual outgoing edge and a continuation at its target at successor length. Every edge, including its parallel-edge number, is retained. ray_refine_disjoint gives disjointness for unequal continuation indices; refined_endpoint is continuationEnd p. The finite cardinality is at most Delta G raised to r, where Delta is max 1 of the maximal outgoing degree. These are arbitrary natural lengths and integer cuts.

**Definition 1.4 (Finite saturated partitions of actual subsets).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \forall U \in \operatorname{Set}\left(\operatorname{History}\left(G\right)\right),\; \operatorname{IsBeam}\left(G, U\right) \Leftrightarrow \left(\exists n \in Int,\; \operatorname{AtCut}\left(G, U, n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.IsBeam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parts G U n is {P : RayAt G n // P.val is a subset of U}. AtCut G U n means Finite (Parts G U n) AND every x in U has its entire ray G x n contained in U. Beam G is the subtype of IsBeam subsets. The finite condition alone would allow selected points and would not supply the required saturation.

Under finite vertex/edge instances, DecidableEq V and Essential G, parts_union and parts_disjoint give the intrinsic disjoint partition. atCut_mono refines it to any later integer cut. Finite unions normalize equal actual ray sets, while distinct rays with coincident endpoints remain separate. If the same ray set occurs at two ordered cuts, equal_ray_unique_continuation proves its numbered refinement has exactly one component.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.IsBeam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.ray`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.ray_refine`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamGeometry.spliceEquiv`
- Dependency: [D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion](FiniteWindowTableCriterion.md)
