# Original side traces, twenty-cell cover and null overlaps

## Abstract

The original twenty closed coefficient cells cover the common six-length cut body and have pairwise null overlaps in its explicit three-coordinate chart.

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

For the overlap application retain these same original twenty tuples and all six strictly positive lengths. No determinant assumption or simplex nondegeneracy is added. Write each point of a cell as a normalized sum of its four vertices with nonnegative coefficients. Two representations with every coefficient strictly positive cannot agree when the cell indices differ. The coefficient argument uses the original eight supports and endpoint incidences, so it does not infer disjointness from a sketch of the fan.

First suppose the two boundary triangles have different facet supports. Each facet vanishes on its own three endpoints and is strictly negative at the common barycenter. It is nonpositive on every endpoint of the other triangle, and the original endpoint-incidence table gives a strictly negative value on at least one of them. Applying that facet to equal positive combinations forces the first barycenter coefficient to be strictly larger than the second. Applying the other facet forces the reverse strict inequality, a contradiction.

If the facet supports agree, evaluating that support first makes the barycenter coefficients equal. Remove the common barycenter contribution. Distinct cells on this facet are two of the four specified side triangles, with the same original root. For each triangle its original ridge support vanishes on its two opposite-edge endpoints and is strictly negative at the root. On the other triangle that support is nonpositive, with at least one strictly negative opposite-edge endpoint. Applying the two ridge supports now forces opposite strict inequalities between the root coefficients. The original facet, ridge and endpoint tables include all twenty indices; a cap facet has only its one triangle.

It follows that every point in the intersection of two distinct closed cells has a zero coefficient in at least one of its two nonnegative normalized representations. Deleting that zero coefficient leaves the convex hull of the other three original vertices. Thus the intersection is contained in the union of the four triangular face hulls of each of the two cells. The argument needs neither affine independence nor an orientation of either four-tuple.

Use the coordinate chart on the common sum-one affine space given by dropping the fourth coordinate: pi(x)=(x_0,x_1,x_2). Its inverse is chi(y)=(y_0,y_1,y_2,1-y_0-y_1-y_2). The original vertices belong to cutBody(l), and convexity of the sum-one affine space puts every cell in that space. Hence pi is injective on all these cells, and pi(cell_n) intersect pi(cell_m) equals pi(cell_n intersect cell_m). This equality is required: an image of an intersection cannot by itself stand for an intersection of images.

For nondegeneracy retain every original ordered tuple p_j=vertices(l,n,j), with all six original lengths strictly positive. The supporting-flag criterion is elementary: suppose linear forms L,R satisfy L(p_0) different from zero, L(p_1)=L(p_2)=L(p_3)=0, R(p_1) different from zero, R(p_2)=R(p_3)=0, and p_2 different from p_3. In a relation sum_j w_j p_j=0 with sum_j w_j=0, applying L first gives w_0=0 and applying R next gives w_1=0. The weight sum gives w_3=-w_2, so the vector relation becomes w_2(p_2-p_3)=0. The distinct last two vertices force w_2=w_3=0. This is the finite weighted-vsub criterion for affine independence.

Apply this criterion to each of the literal twenty rows, using L=support(l,facet(n)) and R=support(l,ridge(n)). The first vertex is always b=(1/4,1/4,1/4,1/4). LengthGramBody.shared_radial_body supplies strict negativity of every Gram-row support at b, while each coordinate support equals -1/4 there. The endpoint classification in LengthGramPolytope.cut_body_polytope supplies exactly the zero and strictly negative entries required by the facet and ridge tables. It also makes the original ordered endpoint map injective; the final two endpoint labels in every row differ. Thus every one of the twenty original four-tuples is affinely independent in the coefficient space. No Gram determinant, Delta condition, independently postulated fan, or nondegeneracy hypothesis is used.

Use the same sum-one chart pi(x)=(x_0,x_1,x_2) and affine inverse chi(y)=(y_0,y_1,y_2,1-y_0-y_1-y_2). The existing body results put every original vertex in the sum-one carrier, so chi(pi(p_j))=p_j. Affine independence of the original tuple therefore implies affine independence of its three-coordinate image. In particular the actual 3 by 3 edge matrix B(l,n), whose column j is pi(vertices(l,n,j+1))-pi(vertices(l,n,0)) for j=0,1,2, has linearly independent columns and det B(l,n) different from zero, for each n in Fin(20). The matrix uses the original row order and the explicit coordinate chart, rather than an unspecified orientation convention.

This identifies a nonzero coordinate determinant for every original cell throughout the domain of six positive lengths. It does not select its sign, prove a common time-dependent orientation, identify two cells' exact common face or opposite outward coefficients, or supply the geometric density and normalized surface measure. Those remain separate steps before affine flux transfer, internal-face cancellation, measured native-volume variation and the Schlaefli identity. The supporting-flag elimination and chart transfer are applications of the existing support, affine-independence and nonsingular-matrix results; no new standalone mathematical declaration or literature priority is asserted.

A linear map sends each three-vertex face hull to the convex hull of three points in R^3. Its affine span is proper, since its affine dimension is at most two; the existing Haar-measure theorem for a proper affine subspace makes that hull Lebesgue-null. The preceding finite union therefore proves that pi(cell_n) intersect pi(cell_m) has three-dimensional Lebesgue measure zero for every n different from m. This is a null-overlap statement in the explicit coefficient chart. Exact pairwise face descriptions, orientation, the geometric measure and density identification, integrability, volume variation and the Schlaefli identity require their separate arguments. These are applications of the existing support, convex-hull, affine-span and Haar-measure results; no new standalone mathematical declaration or literature priority is asserted.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/CapTraceHull.cap_trace_hull`
- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull`
- Truth anchor: `D5/S3/Geometry/Hyperideal/ZeroTraceHull.zero_trace_hull`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
