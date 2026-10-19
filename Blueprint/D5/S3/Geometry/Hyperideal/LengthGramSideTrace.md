# Original side traces and the twenty-cell cover

## Abstract

The original twenty closed coefficient cells cover the common six-length cut body, and each cyclic supporting trace is its original edge segment.

Fix six strictly positive lengths in the original order 01, 02, 03, 23, 13, 12. For a side label k, the side support is the coordinate support x_k=0. The six cyclic supports are the alternating coordinate and Gram-row supports of the three remaining labels.

**Theorem 1.1 (Two supporting traces recover the corresponding closed edge).**

$$cycleEdgeHull$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint support classification identifies exactly two original ordered endpoints on the simultaneous zero trace. The common zero-trace convex-hull lemma then identifies the whole intersection with their convex hull, which is the displayed closed segment. The result concerns the original coefficient body and its original endpoint coordinates.

For the covering application use the original LengthGramSideTrace definitions vertices(l,n), cell(l,n) and boundaryTriangle(l,n), with n in Fin(20). Thus cell is the closed convex hull of the original four-tuple and boundaryTriangle is the closed convex hull of its final three entries. The affine carrier is sum_i x_i=1. The body K=cutBody(l) is cut out by the eight original linear supports L_f(x)<=0: four coordinate supports -x_i and four rows of lengthGram(l). All six lengths are strictly positive; no determinant or Delta condition is needed for this coefficient-space statement.

Here is the finite supporting-ray certificate used twice. For distinct o,x in K let J be the supports with L_f(o)<0 and set t=max_{f in J} L_f(x-o)/(-L_f(o)). There is a coordinate q with x_q<o_q: otherwise nonnegative coordinate differences and the common sum one force x=o. Since x_q>=0, this coordinate gives o_q>0 and a strictly positive ratio in J. The inequalities at x give every ratio at most one, so 0<t<=1. Put z=o+(x-o)/t. Its coordinate sum remains one. For a support in J, maximality gives L_f(z)<=0; for a support outside J, L_f(o)=0 and L_f(z)=L_f(x)/t<=0. A maximizing support vanishes at z and is strictly negative at o. Finally x=(1-t)o+t z, so x lies on the closed segment from o to z. The case x=o is handled directly, without division by t.

The cap exit is supplied by `D5/S3/Geometry/Hyperideal/CapTraceHull.cap_trace_hull`. Its exact endpoint range is the three final vertices of capIndex(i), so a zero Gram-row support puts z in that original cap boundary triangle. The simultaneous zero trace of coordinate support k and Gram-row support k is empty: `D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull` selects endpoints whose first label is k and whose two labels both differ from k, an impossible incidence condition. This excludes that exit without adding a diagonal-disjointness premise.

For a side k, take the original root o=sideCycle(l,k,0) and apply the same certificate within x_k=0. The interpolation formula preserves this coordinate. The supports strictly negative at o are the four cycleSupport(k,r) with r=1,2,3,4, together with Gram row k. The last cannot vanish on this side by the preceding empty-trace argument. The existing cycle_edge_hull therefore puts z on the exact closed segment from sideCycle(l,k,r) to sideCycle(l,k,r+1), for some r in {1,2,3,4}. Consequently x belongs to the convex hull of the original root and those two original consecutive vertices. This hull is exactly boundaryTriangle(l,sideIndex(k,r-1)). The root itself belongs to the first such triangle. These four specified triangles cover the whole side; cyclic convexity or fan coverage is not an extra premise.

The original barycenter b=(1/4,1/4,1/4,1/4) belongs to K by LengthGramBody.shared_radial_body. Apply the certificate with o=b. Every exit point lies either on a cap triangle or on one of the four specified triangles of a side. The original tuple identity gives cell(l,n)=convexJoin R {b} (boundaryTriangle(l,n)), using convexHull_insert. Hence every x in K belongs to one of the literal twenty cells. Conversely the barycenter and every endpoint belong to K, and K is convex by the existing twelve-endpoint hull equality, so each cell is contained in K. Thus cutBody(l) is exactly the union over n in Fin(20) of cell(l,n), for every six strictly positive original lengths.

The conclusion is an exact cover by the original closed convex hulls. Pairwise face intersections, nondegeneracy, orientation and measure-zero overlap still require their own certificates before this cover can be used as an integral decomposition. The covering application establishes no volume-variation formula or Schlaefli identity. It applies the existing endpoint, zero-trace and cyclic-edge results together with finite maximum and convex-join facts; no new standalone mathematical declaration or literature priority is asserted.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CapTraceHull.cap_trace_hull`
- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
