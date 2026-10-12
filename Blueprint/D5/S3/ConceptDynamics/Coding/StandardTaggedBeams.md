# Geometric matching of finite tagged actual beams

## Abstract

Geometric matching of finite tagged actual beams.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Finite tags retain identical copies).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \operatorname{recordType}\left(\operatorname{Object}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.Object` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

recordType denotes the Lean structure being described. Object G has Tag : Type v, finiteTag : Finite Tag, and beam : Tag -> Beam G. Its pieces at n are the dependent sum of each tag and Parts of that tag's actual subset. plus uses disjoint sum of tags, not overlapping set union. Thus two identical copies remain two copies. This makes repeated vertex generators available even for a deterministic graph such as reset q=1, where extra disjoint pasts cannot be presumed. No positive-entropy premise is imposed.

**Definition 1.2 (Define equivalence by endpoint-preserving geometric matching).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \forall A \in \operatorname{Object}\left(G\right), Bobj \in \operatorname{Object}\left(G\right), n \in Int,\; \operatorname{recordType}\left(\operatorname{Matching}\left(G, A, Bobj, n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.Matching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matching G A B n contains left : Normalized G A n, right : Normalized G B n, pieces : Pieces G A n equiv Pieces G B n, and endpoints : forall P, pieceEndpoint(pieces P)=pieceEndpoint P. Normalized says every tagged subset satisfies AtCut at that same integer n. Equivalent G A B is the existence of n with Nonempty (Matching G A B n). Each matched pair is realized by the actual future-preserving spliceEquiv on its two ray subsets. Matching.rows derives row equality. matchingOfRows proves the converse by bijecting finite endpoint fibers; row equality is not the definition of the relation.

**Theorem 1.3 (Coordinate equality is equivalent to actual eventual matching).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \forall A \in \operatorname{Object}\left(G\right), Bobj \in \operatorname{Object}\left(G\right),\; \operatorname{Equivalent}\left(G, A, Bobj\right) \Leftrightarrow \operatorname{objectValue}\left(G, A\right) = \operatorname{objectValue}\left(G, Bobj\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.equivalent_iff_value_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

objectValue G A is the finite sum of beamCoordinate over every tag. The forward direction uses the actual geometric Matching. For the converse, normalize both objects at a common integer cut, advance to a nonnegative stage, and use Module.DirectLimit.exists_eq_of_of_eq to obtain a later stage of equal rows. Numbered refinement produces those rows; matchingOfRows constructs the endpoint-fiber bijection and its past splices. equivalent_iff_common_rows gives the corresponding eventual common-integer-cut criterion.

**Definition 1.4 (Use the real Grothendieck group of the tagged quotient).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{typeAlias}\left(\operatorname{BeamGroup}\left(G, hG\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.BeamGroup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

typeAlias displays the Lean abbreviation. BeamMonoid G hG is Quotient (beamSetoid G hG), with addition induced by plus. BeamGroup G hG is Additive (Algebra.GrothendieckGroup (Multiplicative (BeamMonoid G hG))). intoGroup is the library completion map. F : BeamGroup G hG ->+ RowLimit G extends quotientValue by the actual Mathlib universal property. StandardBeamIdentification constructs J and proves both inverse identities. For a finite DISJOINT same-cut ray union, disjointUnion_group identifies its singleton class with the tagged family of components; this additivity formula is not asserted for an overlapping union.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.BeamGroup`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.Matching`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.Object`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardTaggedBeams.equivalent_iff_value_eq`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates](StandardBeamCoordinates.md)
