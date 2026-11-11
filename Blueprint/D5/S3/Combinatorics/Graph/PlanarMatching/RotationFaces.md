# Actual facial boundaries and cycle sides

## Abstract

Signed-Euler-two actual-dart rotations have exact binary facial boundaries, connected edge-selected cycle sides, regional Euler identities, actual matching restrictions and nice-cycle orientations.

Let V be an arbitrary finite vertex type with decidable equality, G a connected simple graph with decidable adjacency and a nonempty actual dart type, and R a Rotation of G. Assume the signed integer equation card(V) minus card(G.edgeSet) plus card(R.Face) equals two. Use the actual Rotation, complete facial orbits, boundary map and faceOpposition defined in RotationBoundary. Its face_cycle_exact theorem and face-odd construction supply the boundary and orientation inputs below. All cycles, complementary vertex sets, subgraphs and matching restrictions below belong to that same actual graph.

**Theorem 1.1 (Actual cycle sides, edge-selected connected regions and matching restriction).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.cycle_face_sides`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.cycle_face_sides` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

Under exactly the same model hypotheses, fix any vertex a, actual closed walk p from a to a, and proof that p is a simple cycle. There exist a binary face function x and vertex sets I and J. Both a face with x equal to one and a face with x equal to zero exist. B(x) is exactly the unordered-edge indicator of p. There exists q equal to p or p.reverse such that, for every actual dart d, the facial shore values (one,zero) are equivalent to d belonging to q.darts, and (zero,one) are equivalent to d belonging to q.reverse.darts. This identifies both directed side boundaries with the actual cycle traversal or its reversal. The local proof uses the two actual cycle edges at each vertex and the rotor interval between them. For every vertex v, v is outside p.support if and only if v belongs to I or J, and I and J are disjoint. For every actual dart starting outside p.support, its first vertex belongs to I exactly when its face has x-value one, and belongs to J exactly when that value is zero. There is no original G edge between a vertex of I and a vertex of J.

For every pair (S,b) equal to (I,1) or (J,0), an actual subgraph H of G exists. Its vertex set is the union of p.support and S. For every original dart d, H contains the edge of d exactly when it is a cycle edge or both facial shores have x-value b. H is connected. Its signed Euler expression card(H.verts) minus card(H.coe.edgeSet) plus card of the faces with x-value b equals one. Equivalently, card(S) minus the number of selected edges outside the actual cycle edge set plus that same face count equals one. Every subtraction in both identities takes place in the integers. The proof injects functions supported on each proper facial side into the cycle space of its actual edge-selected graph. The existing connected cycle-rank theorem gives two inequalities; the global signed Euler equation and the exact vertex and edge union/intersection counts force equality for both sides. This is an edge-selected subgraph: a chord on the opposite facial side is excluded even when both its endpoints lie on the cycle. The proof connects each off-cycle vertex to the cycle along an original graph walk until it first reaches the cycle, then uses the actual cycle subgraph.

Let M be any subgraph of the actual graph G induced on the vertices outside p.support, and suppose M is a perfect matching. For each S equal to I or J, M restricts to a perfect matching N of the further induced graph on the complement vertices whose original vertex lies in S. For all vertices v,w of that restriction, N.Adj v w if and only if M.Adj v.val w.val. Thus the restriction retains exactly the original matching edges. Both Nat.card I and Nat.card J are even, by the existing IsPerfectMatching.even_card theorem and the explicit vertex-subtype equivalence. No matching on a replacement carrier and no supplied interior parity is used.

**Theorem 1.2 (Face-odd orientations are odd on actual nice even cycles).**

Lean statement: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.face_odd_nice_cycle_orientation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.face_odd_nice_cycle_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Cimasoni, Nicolai Reshetikhin (2007). *Dimers on surface graphs and spin structures. I*. DOI: [10.1007/s00220-007-0302-7](https://doi.org/10.1007/s00220-007-0302-7). URL: <https://arxiv.org/html/math-ph/0608070v2>.

*Commentary.*

For every finite V, connected actual simple graph G with a dart, and Rotation satisfying the signed integer Euler equation, suppose card(V) is even. There exists an actual dart function epsilon with values in ZMod 2. For every actual dart d, epsilon(alpha(d)) equals one plus epsilon(d). For every face f, faceOpposition epsilon f equals one. faceOpposition sums epsilon(d) over all actual darts whose facial class is f, retaining dart multiplicity and every face orbit. For every vertex a and actual simple closed walk p at a of even length, and every actual perfect matching M of G induced on the vertices outside p.support, the sum of epsilon over the list p.darts equals one.

Start with an arbitrary actual orientation and solve its facial defects through the transpose of the binary boundary map. The already proved constant kernel identifies the only compatibility condition: the total defect is zero. The signed global Euler equation and even vertex count prove that condition. The existing algebraic dual-map theorem supplies an edge correction. Applying it to both darts of each edge preserves opposition reversal and makes every facial orbit odd.

The nice-cycle proof consumes cycle_face_sides on that exact G and p. It sums the face equations over one proved side. Each selected internal edge contributes one, and the proved directed boundary contributes the epsilon sum over p or p.reverse. The signed regional Euler identity turns this sum into one plus the off-cycle side cardinality. The actual complement matching restricts through the proved no-cross-edge result, so the existing perfect-matching parity theorem makes that side cardinality even. Reversal preserves the epsilon sum because p has even length. Interior parity, side separation and regional Euler are conclusions of this chain.

The two facial subsets are x inverse-image of one and x inverse-image of zero; binary values make them complementary and both are nonempty. These results establish face-to-cycle exactness, actual side separation, connected edge-selected regions, both regional Euler identities, directed boundaries, matching restriction and the face-odd nice-cycle orientation. Geometric embedding correspondence and arbitrary graph cases, matching-sign transport, compatible Pfaffian expansion, Cayley's identity and nonnegative-weight partition identities including zero cases, rational input and bit complexity, and general bipartite counting complexity remain outside these results. This is an application of mature Kasteleyn theory in the stated finite rotation model; no research originality or full Chapter 30 completion is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.cycle_face_sides`
- Truth anchor: `D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.face_odd_nice_cycle_orientation`
- Dependency: [D5/S3/Combinatorics/Graph/PlanarMatching/RotationBoundary](RotationBoundary.md)
