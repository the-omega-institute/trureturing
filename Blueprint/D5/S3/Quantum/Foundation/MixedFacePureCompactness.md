# Compactness from maximal mixed faces

## Abstract

Proper pure-pair faces and maximal mixed faces close the original pure locus.

**Theorem 1.1 (Closedness and compactness of the whole pure locus).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\mathrm{IsClosed}\left(C\right) \land \left(\left(\forall x \in V,\; \left(x \in C \land x \ne 0\right) \Rightarrow 0 < \mathrm{u}\left(x\right)\right) \land \left(\mathrm{span}\left(\mathbb{R}, C\right) = top \land \left(\mathrm{pairProper}\left(C, u\right) \land \left(\forall F \in \mathrm{Set}\left(V\right),\; \left(\left(\mathrm{Convex}\left(\mathbb{R}, F\right) \land \left(\mathrm{IsExtreme}\left(\mathbb{R}, \mathrm{base}\left(C, u\right), F\right) \land F \ne \mathrm{base}\left(C, u\right)\right)\right) \land \left(\exists x \in V,\; x \in F \land \left(\neg x \in \mathrm{pure}\left(C, u\right)\right)\right)\right) \Rightarrow \left(\forall G \in \mathrm{Set}\left(V\right),\; \left(\left(\mathrm{Convex}\left(\mathbb{R}, G\right) \land \left(\mathrm{IsExtreme}\left(\mathbb{R}, \mathrm{base}\left(C, u\right), G\right) \land G \ne \mathrm{base}\left(C, u\right)\right)\right) \land F \subseteq G\right) \Rightarrow G = F\right)\right)\right)\right)\right)\right) \Rightarrow \left(\mathrm{IsClosed}\left(\mathrm{pure}\left(C, u\right)\right) \land \mathrm{IsCompact}\left(\mathrm{pure}\left(C, u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/MixedFacePureCompactness.pure_closed_compact_of_mixed_face_coatoms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a finite-dimensional real normed space, C a closed spanning pointed cone, and u a real linear unit strictly positive on the nonzero elements of C. Write K for the entire normalized base and P for its full extreme-point set. Assume pairProper(C,u), meaning every two distinct points of P generate a proper actual face of K. Assume also that each proper convex extreme subset of K containing a point outside P is maximal among proper convex extreme subsets of K. Then P is closed and compact in V.

Suppose a sequence in P converges to a mixed point x of the compact base. Fix any pure point q. Eventually the sequence points differ from q. Lift each of their pair faces with q to a proper cone face and take a nonzero linear support, nonnegative on C and zero on that face. Normalize these supports in operator norm. A subsequence converges on the compact dual unit sphere, and joint continuity of evaluation gives a norm-one support e that is nonnegative on C and vanishes at x and q.

The zero slice of e in K is a proper face by the spanning condition. It contains the entire normalized principal face of x because a nonnegative functional vanishing at x vanishes at every cone vector positively dominated by x. This makes the principal face proper. It is closed, and compact convex generation supplies a pure point q outside it. The proper zero slice for this q would strictly contain the principal face, contradicting maximality. Thus P is closed in the compact base and is compact.

The all-label Hit route to compactness uses incidence of distinguishable pure neighbours with every pure-pair face. See `D5/S3/Quantum/Foundation/HitPureCompactness.hit_pure_closed_compact`.

In downstream L2 geometry, closedness of the pure locus is the input used to rule out degeneration of limiting pair ellipsoids in Quantum Origin Binary Normal Differences and Orientation XVII, Theorem 198.6, at source revision 5267f37e2dd8562f3d93ee93d56425d0667626d1.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HitPureCompactness.hit_pure_closed_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/MixedFacePureCompactness.pure_closed_compact_of_mixed_face_coatoms`
- Dependency: [D5/S3/Quantum/Foundation/ExclusionBallFaces](ExclusionBallFaces.md)
- Dependency: [D5/S3/Quantum/Foundation/HitSectionGeneration](HitSectionGeneration.md)
