# Literal stars in the second barycentric subdivision

## Abstract

Literal original second stars equal the union of stars inside complete first parents.

Let R be the real field and E any real normed vector space, with no finite-dimensional restriction. Let p:Fin(4) to E be the original vertex family. Finsets(X) denotes finite subsets of X. IsFaceChain(C) means that C is nonempty, every F in C is a nonempty finite subset of Fin(4), and every two members of C are comparable by inclusion. barycenter(E,p,F) is the sum of p(j) over j in F divided by realCard(F), the cardinality viewed in R. For every permutation pi of Fin(4), prefixFace(pi,k) is the image under pi of positions 0 through k. Write parentVertices(E,p,pi)(k)=barycenter(E,p,prefixFace(pi,k)). For any vertex family q, closedStar(E,q) is the union of convex hulls of face-chain barycenters whose actual vertex set contains q(0); openStar(E,q) uses the intrinsic interior of each such hull. All nonempty dimensions occur in both unions. Intrinsic interior is taken in each hull's own affine span.

**Definition 1.1 (Original chains of original face chains).**

$$\forall D \in Finsets\left(Finsets\left(Finsets\left(Fin\left(4\right)\right)\right)\right),\; (IsSecondFaceChain\left(D\right)) \iff ((Nonempty\left(D\right)) \land ((\forall C \in Finsets\left(Finsets\left(Fin\left(4\right)\right)\right),\; (C \in D) \implies (IsFaceChain\left(C\right))) \land (\forall C \in Finsets\left(Finsets\left(Fin\left(4\right)\right)\right),\; \forall B \in Finsets\left(Finsets\left(Fin\left(4\right)\right)\right),\; ((C \in D) \land (B \in D)) \implies ((subset\left(C, B\right)) \lor (subset\left(B, C\right))))))$$

*Formalization.* `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.SecondFaceChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is a nonempty finite family of original nonempty face chains C. Inclusion between two C's compares sets of original faces; it does not compare their unions of original vertices. Both levels include every nonempty dimension.

**Definition 1.2 (Average of actual first barycenters).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall C \in Finsets\left(Finsets\left(Fin\left(4\right)\right)\right),\; secondBarycenter\left(E, p, C\right) = smul\left(inverse\left(realCard\left(C\right)\right), sumFaceBarycenters\left(E, p, C\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.secondBarycenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sumFaceBarycenters(E,p,C) sums barycenter(E,p,F) over F in C. Thus the two averaging operations keep their respective cardinalities. This is not the barycenter of the union of C.

**Definition 1.3 (Actual second subdivision simplex).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall D \in SecondFaceChain,\; secondHull\left(E, p, D\right) = convexHull\left(R, secondVertices\left(E, p, D\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.secondHull` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

secondVertices(E,p,D) is the image of D.chains under secondBarycenter(E,p). All sets lie in the same E.

**Definition 1.4 (Literal original closed star).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall i \in Fin\left(4\right),\; \forall x \in E,\; (x \in literalClosedStar\left(E, p, i\right)) \iff (\exists D \in SecondFaceChain,\; (p\left(i\right) \in secondVertices\left(E, p, D\right)) \land (x \in secondHull\left(E, p, D\right))))$$

*Formalization.* `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literalClosedStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index condition requires the actual point p(i) in secondVertices(E,p,D). No parent union occurs in this definition.

**Definition 1.5 (Literal all-face open star).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall i \in Fin\left(4\right),\; \forall x \in E,\; (x \in literalOpenStar\left(E, p, i\right)) \iff (\exists D \in SecondFaceChain,\; (p\left(i\right) \in secondVertices\left(E, p, D\right)) \land (x \in intrinsicInterior\left(R, secondHull\left(E, p, D\right)\right))))$$

*Formalization.* `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literalOpenStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union uses the intrinsic interior of each actual second hull, including the singleton hull at the old vertex.

**Theorem 1.6 (Literal stars and complete first parents).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall i \in Fin\left(4\right),\; \forall x \in E,\; (AffineIndependent\left(R, p\right)) \implies (((x \in literalClosedStar\left(E, p, i\right)) \iff (\exists pi \in Perm\left(Fin\left(4\right)\right),\; (pi\left(0\right) = i) \land (x \in closedStar\left(E, parentVertices\left(E, p, pi\right)\right)))) \land ((x \in literalOpenStar\left(E, p, i\right)) \iff (\exists pi \in Perm\left(Fin\left(4\right)\right),\; (pi\left(0\right) = i) \land (x \in openStar\left(E, parentVertices\left(E, p, pi\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literal_second_closed_and_open_star_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an affinely independent original family p, a second barycenter equals p(i) precisely when its original face chain is the singleton {{i}}. Expand the nested average in the original affine coordinates. Every inner and outer averaging weight is positive. A face containing j different from i would give a positive j coordinate, contradicting uniqueness of the original affine coefficients. The convex-hull version chooses a positive coefficient in a convex representation and obtains the same singleton chain. Hence p(i) belongs to a second hull precisely when {{i}} belongs to its original D.

Choose a maximum first chain in D and refine its increasing series with mathlib's LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot. The returned embedding retains the original faces. Boolean-lattice covers insert one vertex, so their cardinalities recover a permutation and the four nonempty prefix faces. Retention of {i} forces the first vertex to be i. This is an application of the existing chain-refinement theorem.

Within a complete parent pi, map S to the chain of prefixFace(pi,k) for k in S. The inverse selects exactly those k whose prefix face lies in C. Distinct prefix cardinalities make this a cardinality-preserving inverse correspondence. Reindexing the actual finite sums identifies each nested barycenter with the existing parent-face barycenter. Both carrier directions preserve the actual vertex set, therefore the hull and its intrinsic interior. For the closed implication the same retained-chain refinement is applied a second time to the parent face chain. Its complete second flag contains every old second vertex, including p(i), and convex-hull monotonicity retains the original closed face. The open implication keeps the original nonmaximal hull exactly; no monotonicity of intrinsic interiors is used.

The displayed equivalences quantify over all ambient points and all original vertices. They supply the original-carrier bridge to the earlier parent-star characterization. Zero weights, ties and lower-dimensional faces remain inside the definitions. The further radial normalization, coefficient zero-extension identification, deleted-link identification across overlapping parents, and marked retained-quotient identification are distinct propositions; this theorem alone does not assert them or a homeomorphism to a specified manifold.

## References

- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.SecondFaceChain`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literalClosedStar`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literalOpenStar`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.literal_second_closed_and_open_star_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.secondBarycenter`
- Truth anchor: `D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.secondHull`
- Dependency: [D5/S3/Geometry/Gluing/BarycentricSubdivisionStar](BarycentricSubdivisionStar.md)
