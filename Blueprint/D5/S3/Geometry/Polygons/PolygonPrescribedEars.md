# Exact native realization

## Abstract

Prescribed complete ears of a cyclic triangulation

The vertices are ZMod(n), chords are unordered pairs Sym2(ZMod(n)), and a triangulation is a finite set of internal diagonals that is pairwise noncrossing and maximal: each missing internal diagonal crosses a member. EarCenters(T) is the complete set of i for which the chord joining i-1 to i+1 belongs to T. Compatible(P) means that the distinct prescribed ear chords do not cross. V(n)=ZMod(n), Symtwo denotes Sym2, F(n)=Finset(Sym2(V(n))), and natSub is natural subtraction. The prescribed complete-ear existence statement appears in AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B33.3 and B37.2; the same-family path-fibre application appears in B37.7.

**Theorem 1.1 (Every compatible prescribed complete ear set).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((14 \leq n) \implies (\forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Compatible}\left(P\right) \implies ((3 \leq \operatorname{card}\left(P\right)) \implies ((6 \leq \operatorname{natSub}\left(n, \operatorname{card}\left(P\right)\right)) \implies (\exists T \in \operatorname{Finset}\left(\operatorname{Symtwo}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; (\operatorname{IsTriangulation}\left(T\right) \land (\operatorname{EarCenters}\left(T\right) = P))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonPrescribedEars.prescribed_complete_ears` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotate one prescribed centre to 1. For two prescribed nonadjacent centres 1 and k+1, use the integer interval double fan with chords (0,j), 2<=j<=k, and (k,j), k+2<=j<=n-1. The two sets do not interleave. Every missing diagonal interleaves one of these chords, so their union is maximal. Its only ear centres are 1 and k+1, including the cyclic seam case k=n-2. The interval-to-cyclic triangulation bijection transports this construction to the native chord carrier.

For more prescribed centres, delete one prescribed ear and relabel the others through forcedOneEquiv. Their cardinality decreases by one and they remain compatible. Apply the construction recursively while the number of remaining vertices minus the number of prescribed centres stays at least six. Inserting the ear gives every prescribed original ear. Applying the same deletion map to the entire ear set of the inserted triangulation bounds its cardinality by that of P; containment therefore gives equality. Undoing the rotation restores the original labels.

For a path trace P=M_i union {x} contained in the six-ear set D and disjoint from another matching M_j, this triangulation has no ear in common with a triangulation V whose exact D trace is M_j. Indeed EarCenters(T)=P is contained in D, so its intersection with EarCenters(V) is P intersect M_j, which is empty. If V lies in an intersecting family, T is absent from that same family and the whole exact path-trace fibre is not filled. Together with the strict complementary-pair bound, the two path pairs give t_i<=2w3-2 and path loss at least two per group. Uniform omitted-capacity bounds and the final strong twenty-vertex estimate require separate inputs. The construction assumes only cyclic labels and does not assert an affine or Euclidean realization.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonPrescribedEars.prescribed_complete_ears`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCatalanSupplier](PolygonCatalanSupplier.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonConditionedFan](PolygonConditionedFan.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarContraction](PolygonEarContraction.md)
