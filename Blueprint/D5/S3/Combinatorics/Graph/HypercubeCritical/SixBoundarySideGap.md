# The six-boundary side gap

## Abstract

An actual six-boundary bipartite induced subgraph of Q9 has order two, four, or at least twenty-eight.

The object is a finite set C of vertices of Q9 with its actual induced graph. Its actual bipartition L,R covers all vertices. Every vertex of L has degree three; every vertex of R has degree at most three. The extended girth is at least eight, and R has exactly two more vertices than L. There is no balance, connectivity, height, or Clifford hypothesis and no supplied auxiliary graph.

Put e=card(L), o=card(R)=e+2, and let n_j count the actual degree-j vertices of R. The existing GirthSliceCounting path injection gives 3e+2 sum_R d(d-1) at most eo. Actual incidence counting gives sum_j n_j=o and n_1+2n_2+3n_3=3e. Hence 13e+12n_0+4n_1 is at most e squared plus 24. Degrees on R are also at most e. These relations exclude e=2 through e=10. The cases e=0 and e=1 give orders two and four, and e at least thirteen gives order at least twenty-eight.

An L root with three degree-three R neighbors has twelve actual nonbacktracking three-step endpoints and three distinct one-step endpoints. Girth makes all fifteen distinct. Thus for o less than fifteen each L root has at most two degree-three R neighbors. At e=11 the degree counts force six degree-two and seven degree-three R vertices. Exactly one L vertex has one high neighbor; the other ten have two. Those ten actual L vertices label the edges of a simple triangle-free graph on the seven high R vertices. One core vertex has degree two and all others degree three. Each ordinary L label has a degree-two middle and a partner label. Girth forbids common endpoints and cross edges between ordinary partners. An edge incident to the deficient core vertex cannot partner the exceptional label, since they share its unique high neighbor. Its closed-neighborhood union has five vertices. The only two possible partner endpoints would each have two further neighbors in a three-element set. Their neighbor sets are disjoint by triangle-freeness, contradicting four at most three.

At e=12 the same root bound and incidence count force six degree-two and eight degree-three R vertices, with exactly two high neighbors at every L vertex. The core is cubic and triangle-free on eight vertices and every edge has an induced-disjoint partner. A constructive local labeling begins with an edge u-v and its partner x-y. Their neighborhood unions determine complementary two-color partitions of the other four vertices. Choose a adjacent to u,x; its third neighbor c must be adjacent to v,y. The remaining vertices b,d are adjacent to u,v respectively and to each other. If b is adjacent to y, the edge u-a has only y,d as potential partner endpoints, and these are nonadjacent. Thus b is adjacent to x and d to y, giving the exact cube neighbor table. This is a graph construction, not an assumed classification or a graph enumeration. Finite index-table checks only verify the resulting labeling.

The actual degree-two middles pair antipodal parallel core edges. Select the core hexagon 000,100,110,111,011,001. Its six edge labels, six vertex labels and three antipodal-pair middles form an actual induced fifteen-point once-subdivision of K3,3. The omitted high point 010 is connected by three actual two-step paths to the ring middles 000,110,011. Their branch pairs form a perfect matching. Existing CubicalSubdivisionRigidity.normal_labels supplies the six distinct directions. The existing private NineteenPointSlice.three_matching_centers argument, through labelled_matching_obstruction, forces the omitted point to be the origin. It would then have all six selected branches as neighbors, contradicting its original degree bound three. The three bridge labels may have degree three; only their two path adjacencies enter the distance argument.

This repository-derived extremal lemma is motivated by Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2. It does not settle f2(Q9), classify arbitrary 54-vertex objects, resolve the remaining mixed six-saturation cases, or exclude 258 vertices. The original-telescope four-slot information-escape registration remains subject to the concrete realization, variation, sensitivity, readout and binding gap tracked in https://github.com/the-omega-institute/trureturing/issues/31190; this narrative is not a declared_validated registration.

**Theorem 1.1 (The actual six-boundary side gap in Q9).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap.six_boundary_side_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap.six_boundary_side_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual induced graph on C in Q9, an exhaustive bipartition with left degree three, right degree at most three, extended girth at least eight, and card(R)=card(L)+2 implies card(C)=2 or card(C)=4 or 28 at most card(C). All counting, auxiliary graph structure, edge pairing, induced subdivision and cubical distance inputs are derived from these assumptions. The mathematical content lies in the seven-vertex partner obstruction and constructive cubical exclusion of the twelve-left-vertex case.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap.six_boundary_side_gap`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCubical](SixBoundarySideCubical.md)
