# Literal successor coordinates

## Abstract

An actual Boolean successor coordinate and all-pairs literal Prefix extension from an arbitrary closed cover.

Use the original SignedProperLimit core: Coord(a) is Iio(a), Cube(a) is Coord(a) to Bool, and restrict is literal precomposition with ordinal inclusion. For an arbitrary ordinal a, H is a Prefix(succ(a)), top(a) is the index a<succ(a), and K is H.Space(top(a)). Y and Z are closed subsets of K with union K. The actual splitCarrier(Y,Z) consists of (k,false) for k in Y and (k,true) for k in Z. Overlap retains two separate points. Either side may be empty, and a may be zero.

**Theorem 1.1 (Closed-cover insertion and complete Prefix extension).**

$$\forall a: Ordinal0, \forall H: \operatorname{Prefix}\left(\operatorname{succ}\left(a\right)\right), \forall Y: \operatorname{Set}\left(\operatorname{Space}\left(H, \operatorname{top}\left(a\right)\right)\right), \forall Z: \operatorname{Set}\left(\operatorname{Space}\left(H, \operatorname{top}\left(a\right)\right)\right), \operatorname{IsClosed}\left(Y\right) \Rightarrow \operatorname{IsClosed}\left(Z\right) \Rightarrow \operatorname{Eq}\left(\operatorname{union}\left(Y, Z\right), univ\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{Result}\left(H, Y, Z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedSuccessorCoordinates.exists_successor_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Result(H,Y,Z) supplies a closed nonempty carrier C in Cube(succ(a)), an actual homeomorphism e from splitCarrier(Y,Z) onto C, and a Prefix(succ(succ(a))). C is exactly the range of the insertion. For every split point ((k,b),proof) and every i<succ(a), insertion reads k(i) if i<a, and b otherwise; in the latter case i=a. The old-coordinate equation holds at every i<a, the coordinate a is exactly b, and restricting e(x) to a gives k exactly. The inverse reads the old restriction and coordinate a. The homeomorphism proves continuity and both inverse equations.

Every old carrier at b<succ(a) is retained as the same set in Cube(b). The new carrier at succ(a) is exactly C. For every b<=a and every z in C, restricting z to b equals restricting the first coordinate of e inverse(z) to b. This equality is used to construct compatibility at every old/new pair. Old/old compatibility and surjectivity come directly from H. For an old/new pair, H.onto first lifts to stage a; the actual cover then supplies a Boolean sheet. Inserting that split point gives the required preimage by the exact restriction equation. Equal new stages use the identity. These are the actual compatible and onto fields of the output Prefix, for all pairs in its domain.

Mathlib's Homeomorph.funSplitAt and Homeomorph.piCongrLeft supply function-space splitting and reindexing after identifying the complement of the last ordinal coordinate with Coord(a). Continuous.isClosedEmbedding and Topology.IsEmbedding.toHomeomorph turn the actual continuous injective split insertion into the range homeomorphism. Closedness follows from compactness of the actual closed split inside K times Bool and the Hausdorff target cube. Nonemptiness uses K's existing nonemptiness and the cover's first-projection surjectivity. The new construction is the ordinal coordinate identification and the complete dependent Prefix assembly; the standard topology results and existing Prefix are reused.

This local topology supplier assumes no CH, countability, metric structure, proper-stage condition or signed measure system. It does not provide measure transport, a full successor measure system, transfinite recursion, CH bookkeeping or the final topological and analytic endpoints. The construction is repository-derived; no literature novelty or full CH solution is asserted.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedSuccessorCoordinates.exists_successor_coordinates`
- Dependency: [D5/S3/Topology/InverseLimit/SignedProperLimit](SignedProperLimit.md)
- Dependency: [D5/S3/Topology/Measures/SignedSplitSuccessorSupport](../Measures/SignedSplitSuccessorSupport.md)
