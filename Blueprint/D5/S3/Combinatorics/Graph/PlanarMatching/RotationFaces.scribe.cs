using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PlanarMatching;

internal sealed class RotationFacesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/cimasoni2007dimers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-Euler-two actual-dart rotations have exact binary facial boundaries, connected edge-selected cycle sides, regional Euler identities and actual matching restrictions.",
        H("Actual facial boundaries and cycle sides"),
        Blocks(
            Paragraph(Text(
                "Let V be an arbitrary finite vertex type with decidable equality, and G a connected simple graph on V with decidable adjacency and at least one actual dart. "
                + "Rotation G consists of a permutation rho of G.Dart whose SameCycle classes are precisely the darts with a common first vertex. "
                + "Reversal alpha sends a dart to its symm. The facial successor phi first reverses a dart and then applies rho. "
                + "Face is the quotient by SameCycle phi, using integer powers and retaining every orbit, including singleton orbits. "
                + "The edge type E is G.edgeSet, the subtype of actual unordered edges. No side, surface realization or parity property is included in Rotation.")),
            Paragraph(Text(
                "The boundary linear map B takes a face function x with values in ZMod 2 to the edge function whose value is the sum of the two facial shore values. "
                + "Its definition chooses an actual representative dart of each unordered edge. Its evaluation theorem proves that the sum is independent of that choice. "
                + "Every cardinality in the Euler hypothesis is cast to the integers before subtraction: card(V) minus card(E) plus card(Face) equals two.")),
            Describe.Lean(DescribeId.Create("face-cycle-exact"),
                DeclarationHandle.Create(Prefix + "face_cycle_exact"),
                H("The face boundary map is exact onto the actual cycle space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite V, G and Rotation satisfying the stated connectedness, actual-dart nonemptiness and signed integer Euler equation, three conclusions hold together. "
                        + "For every face function x and actual dart d, B(x) on the unordered edge of d is x(face d) plus x(face alpha(d)). "
                        + "For every x, B(x) is zero if and only if there exists c in ZMod 2 such that x is the constant function with value c. "
                        + "The linear range of B equals SimpleGraphCycleSpace.simpleCycleSpace G, the existing span of indicators of actual simple cycles.")),
                    Paragraph(Text(
                        "Zero boundary equates opposite shore values. Facial succession then equates values after a rotor step, and an actual graph walk propagates this equality between all faces. "
                        + "Reindexing a dart sum along phi proves that every facial boundary annihilates the vertex-to-edge differential. "
                        + "The frozen finite_graph_cycle_space theorem identifies these relations with the existing cycle space. "
                        + "Rank-nullity, the one-dimensional constant kernel and the signed Euler equation establish equality of the two subspaces. "
                        + "Generic cycle rank and linear algebra are reused; geometric separation is not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-face-sides"),
                DeclarationHandle.Create(Prefix + "cycle_face_sides"),
                H("Actual cycle sides, edge-selected connected regions and matching restriction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Under exactly the same model hypotheses, fix any vertex a, actual closed walk p from a to a, and proof that p is a simple cycle. "
                        + "There exist a binary face function x and vertex sets I and J. Both a face with x equal to one and a face with x equal to zero exist. "
                        + "B(x) is exactly the unordered-edge indicator of p. There exists q equal to p or p.reverse such that, for every actual dart d, "
                        + "the facial shore values (one,zero) are equivalent to d belonging to q.darts, and (zero,one) are equivalent to d belonging to q.reverse.darts. "
                        + "This identifies both directed side boundaries with the actual cycle traversal or its reversal. The local proof uses the two actual cycle edges at each vertex and the rotor interval between them. "
                        + "For every vertex v, v is outside p.support if and only if v belongs to I or J, and I and J are disjoint. "
                        + "For every actual dart starting outside p.support, its first vertex belongs to I exactly when its face has x-value one, and belongs to J exactly when that value is zero. "
                        + "There is no original G edge between a vertex of I and a vertex of J.")),
                    Paragraph(Text(
                        "For every pair (S,b) equal to (I,1) or (J,0), an actual subgraph H of G exists. "
                        + "Its vertex set is the union of p.support and S. For every original dart d, H contains the edge of d exactly when it is a cycle edge or both facial shores have x-value b. "
                        + "H is connected. Its signed Euler expression card(H.verts) minus card(H.coe.edgeSet) plus card of the faces with x-value b equals one. "
                        + "Equivalently, card(S) minus the number of selected edges outside the actual cycle edge set plus that same face count equals one. "
                        + "Every subtraction in both identities takes place in the integers. The proof injects functions supported on each proper facial side into the cycle space of its actual edge-selected graph. "
                        + "The existing connected cycle-rank theorem gives two inequalities; the global signed Euler equation and the exact vertex and edge union/intersection counts force equality for both sides. "
                        + "This is an edge-selected subgraph: a chord on the opposite facial side is excluded even when both its endpoints lie on the cycle. "
                        + "The proof connects each off-cycle vertex to the cycle along an original graph walk until it first reaches the cycle, then uses the actual cycle subgraph.")),
                    Paragraph(Text(
                        "Let M be any subgraph of the actual graph G induced on the vertices outside p.support, and suppose M is a perfect matching. "
                        + "For each S equal to I or J, M restricts to a perfect matching N of the further induced graph on the complement vertices whose original vertex lies in S. "
                        + "For all vertices v,w of that restriction, N.Adj v w if and only if M.Adj v.val w.val. "
                        + "Thus the restriction retains exactly the original matching edges. Both Nat.card I and Nat.card J are even, by the existing IsPerfectMatching.even_card theorem and the explicit vertex-subtype equivalence. "
                        + "No matching on a replacement carrier and no supplied interior parity is used."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The two facial subsets are x inverse-image of one and x inverse-image of zero; binary values make them complementary and both are nonempty. "
                + "These results establish face-to-cycle exactness, actual side separation, connected edge-selected regions and matching restriction. "
                + "They do not establish existence of the face-odd and nice-cycle-odd orientation. "
                + "Those are necessary remaining statements for the complete orientation prerequisite. Geometric embedding correspondence, matching-sign transport, the Pfaffian expansion, Cayley's identity, nonnegative weights, rational bit complexity and general bipartite counting complexity also remain outside these results."))), []));
}
