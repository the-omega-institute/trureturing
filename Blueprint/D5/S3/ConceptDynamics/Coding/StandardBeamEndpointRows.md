# Integer endpoint multiplicity from actual numbered refinement

## Abstract

Integer endpoint multiplicity from actual numbered refinement.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Count outgoing edges with multiplicity).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right),\; \forall u \in V,\; \operatorname{adjacency}\left(G\right)\left(u\right) = \operatorname{outgoingBasisSum}\left(G, u\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.adjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

adjacency G is Matrix V V Int. outgoingBasisSum(u) is the sum over e : {e:E // G.source e=u} of Pi.single (G.target e.val) 1. Each parallel numbered edge contributes separately. wordRow sums the endpoint basis vector of every length-r Continuation; wordRow_eq_pow computes it as Pi.single u 1 multiplied on the right by adjacency G raised to r.

**Definition 1.2 (One integer basis contribution per intrinsic ray).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right),\; \forall U \in \operatorname{Set}\left(\operatorname{History}\left(G\right)\right), n \in Int, finiteParts \in \operatorname{Finite}\left(\operatorname{Parts}\left(G, U, n\right)\right),\; \operatorname{endpointRow}\left(G, U, n\right) = \operatorname{intrinsicEndpointSum}\left(G, U, n\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.endpointRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

intrinsicEndpointSum is the finite sum over P : Parts G U n of Pi.single (RayAt.endpoint G P.val) 1, an element of V -> Int. The finiteParts binder is the local Finite instance required by endpointRow. Multiple distinct pasts ending at the same vertex increase that integer coefficient. An actual finite disjoint union of same-cut rays has exactly one term per union index by endpointRow_disjointUnion; the disjointness premise is essential for that formula.

**Theorem 1.3 (The actual row advances on the right by each nonnegative power).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \forall U \in \operatorname{Set}\left(\operatorname{History}\left(G\right)\right), n \in Int, hU \in \operatorname{AtCut}\left(G, U, n\right), r \in Nat,\; \operatorname{endpointRow}\left(G, U, \operatorname{laterCut}\left(n, r\right)\right) = \operatorname{rightMultiply}\left(\operatorname{endpointRow}\left(G, U, n\right), \operatorname{power}\left(\operatorname{adjacency}\left(G\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.endpointRow_refine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

laterCut(n,r) is n+(r:Int); rightMultiply is Matrix.vecMul, so c_(n+r)=c_n B^r. The endpointRow calls install the Finite instances from hU and atCut_mono hG hU. refinementNumbering bijects the finer Parts with the dependent sum over each earlier actual part of its numbered continuations. This proves the row recurrence for the same actual subset, keeping both repeated endpoints and edge multiplicity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.adjacency`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.endpointRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows.endpointRow_refine`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamGeometry](StandardBeamGeometry.md)
