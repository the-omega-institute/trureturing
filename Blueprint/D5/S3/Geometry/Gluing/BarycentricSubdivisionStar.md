# Stars in the geometric barycentric subdivision of a tetrahedron

## Abstract

Actual face-chain stars are characterized by weak and strict parent coordinate maxima.

Let R denote the real field, and let E be any real normed vector space. The ambient space need not have finite dimension. Fix an affinely independent family p indexed by Fin(4). Its parent simplex is the convex hull of its four vertices. A parent face is a nonempty finite subset of Fin(4). A face chain is a nonempty finite collection of parent faces, any two of which are comparable by inclusion. Every chain dimension is allowed, including singleton chains.

**Definition 1.1 (Chains of actual parent faces).**

$$\forall C \in Finsets\left(Finsets\left(Fin\left(4\right)\right)\right),\; (IsFaceChain\left(C\right)) \iff ((Nonempty\left(C\right)) \land ((\forall F \in Finsets\left(Fin\left(4\right)\right),\; (F \in C) \implies (Nonempty\left(F\right))) \land (\forall F \in Finsets\left(Fin\left(4\right)\right),\; \forall G \in Finsets\left(Fin\left(4\right)\right),\; ((F \in C) \land (G \in C)) \implies ((subset\left(F, G\right)) \lor (subset\left(G, F\right))))))$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.FaceChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FaceChain is the type of collections C satisfying the displayed conditions, together with proofs of those conditions. Finsets(X) denotes finite subsets of X. Nonempty means existence of an element; subset is ordinary inclusion. The faces projection forgets the proofs.

**Definition 1.2 (Geometric face barycenters).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall F \in Finsets\left(Fin\left(4\right)\right),\; barycenter\left(E, p, F\right) = smul\left(inverse\left(realCard\left(F\right)\right), faceSum\left(E, p, F\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.barycenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

realCard(F) is the cardinality viewed in R, faceSum(E,p,F) is the sum of p(i) over i in F, and smul is scalar multiplication. The formula defines the barycenter for every finite F; only nonempty F occur in chains.

**Definition 1.3 (The actual chain simplex).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall C \in FaceChain,\; chainHull\left(E, p, C\right) = convexHull\left(R, vertices\left(E, p, C\right)\right))$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.chainHull` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

vertices(E,p,C) is exactly the image of C.faces under F mapped to barycenter(E,p,F). Thus chainHull is the convex hull of actual geometric barycenters, independently of any coordinate comparison.

**Definition 1.4 (Union of all incident closed chain simplices).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall x \in E,\; (x \in closedStar\left(E, p\right)) \iff (\exists C \in FaceChain,\; (p\left(0\right) \in vertices\left(E, p, C\right)) \land (x \in chainHull\left(E, p, C\right))))$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.closedStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Incidence is geometric: p(0) must belong to the barycenter vertex set of the chain. Affine independence forces a face whose barycenter is p(0) to be the singleton face containing 0.

**Definition 1.5 (Union of all incident intrinsic interiors).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall x \in E,\; (x \in openStar\left(E, p\right)) \iff (\exists C \in FaceChain,\; (p\left(0\right) \in vertices\left(E, p, C\right)) \land (x \in intrinsicInterior\left(R, chainHull\left(E, p, C\right)\right))))$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.openStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

intrinsicInterior(R,Q) is the interior computed in Q's own affine span and then included in E. The union ranges over all incident chains, including lower-dimensional faces and the singleton at p(0). It is not restricted to interiors of maximal subdivision simplices.

For beta:Fin(4) to R, sum(beta) is the sum of its four entries, and pointSum(E,p,beta) is the sum of beta(i) times p(i). Nonnegative entries with sum one ensure this point lies in the parent convex hull. The displayed theorem imposes no further assumption on the point. Ties and zero coefficients are retained. The star characterization is the vertex case of Lemma 2.6, pages 56–57, in the cited source. Here the closed star is expressed directly as the finite union of incident closed simplices.

**Theorem 1.6 (Weak maximum for the closed star; strict maximum for the all-face open star).**

$$\forall E \in Types,\; (RealNormedVectorSpace\left(E\right)) \implies (\forall p \in Fin\left(4\right) \to E,\; \forall beta \in Fin\left(4\right) \to R,\; \forall x \in E,\; ((AffineIndependent\left(R, p\right)) \land ((\forall j \in Fin\left(4\right),\; 0 \le beta\left(j\right)) \land ((sum\left(beta\right) = 1) \land (x = pointSum\left(E, p, beta\right))))) \implies (((x \in closedStar\left(E, p\right)) \iff (\forall j \in Fin\left(4\right),\; (j \neq 0) \implies (beta\left(j\right) \le beta\left(0\right)))) \land ((x \in openStar\left(E, p\right)) \iff (\forall j \in Fin\left(4\right),\; (j \neq 0) \implies (beta\left(j\right) < beta\left(0\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.actual_closed_and_open_star_iff` (`✓ std3`). ∎

*Citation.* Hans Delfs and Manfred Knebusch (1984). *Separation, retractions and homotopy extension in semialgebraic spaces*. DOI: [10.2140/pjm.1984.114.47](https://doi.org/10.2140/pjm.1984.114.47). URL: <https://msp.org/pjm/1984/114-1/p03.xhtml>.

*Commentary.*

For an arbitrary incident chain, the barycenter incidence condition forces its singleton face {0}, and comparability forces every other face to contain 0. Each barycenter therefore has coordinate 0 at least as large as every other coordinate. Convex combinations and uniqueness of parent affine coefficients establish the closed-star implication.

Conversely, sort the parent coefficients in decreasing order, breaking ties by the original index. A maximum at 0 makes 0 first. The actual prefix face barycenters receive weights beta(pi(0))-beta(pi(1)), twice the difference beta(pi(1))-beta(pi(2)), three times the difference beta(pi(2))-beta(pi(3)), and four times beta(pi(3)). These nonnegative weights sum to one and reconstruct every parent coordinate by a triangular identity. The same triangular transformation proves affine independence of the prefix barycenters.

Under strict dominance the first weight is positive. Keep precisely the positive weights and their prefix faces. This is an actual face chain still incident to p(0). In the direction space of its affine span the barycenters form an affine basis. The affine-basis interior theorem and affine-isometry transport place their positive combination in the intrinsic interior. This argument includes a zero-dimensional affine span.

For necessity in the open star, a relative-interior point admits a short extension away from p(0) that remains in its chain hull. If any other parent coordinate were tied with coordinate 0, this extension would make that coordinate larger than coordinate 0, contradicting the closed-star implication. Thus all three comparisons are strict.

**Definition 1.7 (Complete original parent flags).**

$$\forall pi \in Perm\left(Fin\left(4\right)\right),\; \forall k \in Fin\left(4\right),\; prefixFace\left(pi, k\right) = image\left(pi, Iic\left(k\right)\right)$$

*Formalization.* `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.prefixFace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Iic(k) consists of positions from 0 through k. Its image under pi is an original face with k+1 vertices. Write parentVertices(E,p,pi)(k)=barycenter(E,p,prefixFace(pi,k)). These are actual first-level barycenters in E; in particular the zeroth is p(pi(0)).

## References

- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.FaceChain`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.actual_closed_and_open_star_iff`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.barycenter`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.chainHull`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.closedStar`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.openStar`
- Truth anchor: `D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.prefixFace`
