using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PlanarMatching;

internal sealed class RotationFacesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PlanarMatching/RotationFaces.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/RibbonEmbeddings/cimasoni2007dimers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-Euler-two actual-dart rotations have exact binary facial boundaries, connected edge-selected cycle sides, regional Euler identities, actual matching restrictions and nice-cycle orientations.",
        H("Actual facial boundaries and cycle sides"),
        Blocks(
            Paragraph(Text("Let V be an arbitrary finite vertex type with decidable equality, G a connected simple graph with decidable adjacency and a nonempty actual dart type, and R a Rotation of G. Assume the signed integer equation card(V) minus card(G.edgeSet) plus card(R.Face) equals two. Use the actual Rotation, complete facial orbits, boundary map and faceOpposition defined in RotationBoundary. Its face_cycle_exact theorem and face-odd construction supply the boundary and orientation inputs below. All cycles, complementary vertex sets, subgraphs and matching restrictions below belong to that same actual graph.")),
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
            Describe.Lean(DescribeId.Create("face-odd-nice-cycle-orientation"),
                DeclarationHandle.Create(Prefix + "face_odd_nice_cycle_orientation"),
                H("Face-odd orientations are odd on actual nice even cycles"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every finite V, connected actual simple graph G with a dart, and Rotation satisfying the signed integer Euler equation, suppose card(V) is even. "
                        + "There exists an actual dart function epsilon with values in ZMod 2. For every actual dart d, epsilon(alpha(d)) equals one plus epsilon(d). "
                        + "For every face f, faceOpposition epsilon f equals one. faceOpposition sums epsilon(d) over all actual darts whose facial class is f, retaining dart multiplicity and every face orbit. "
                        + "For every vertex a and actual simple closed walk p at a of even length, and every actual perfect matching M of G induced on the vertices outside p.support, "
                        + "the sum of epsilon over the list p.darts equals one.")),
                    Paragraph(Text(
                        "Start with an arbitrary actual orientation and solve its facial defects through the transpose of the binary boundary map. "
                        + "The already proved constant kernel identifies the only compatibility condition: the total defect is zero. The signed global Euler equation and even vertex count prove that condition. "
                        + "The existing algebraic dual-map theorem supplies an edge correction. Applying it to both darts of each edge preserves opposition reversal and makes every facial orbit odd.")),
                    Paragraph(Text(
                        "The nice-cycle proof consumes cycle_face_sides on that exact G and p. It sums the face equations over one proved side. "
                        + "Each selected internal edge contributes one, and the proved directed boundary contributes the epsilon sum over p or p.reverse. "
                        + "The signed regional Euler identity turns this sum into one plus the off-cycle side cardinality. "
                        + "The actual complement matching restricts through the proved no-cross-edge result, so the existing perfect-matching parity theorem makes that side cardinality even. "
                        + "Reversal preserves the epsilon sum because p has even length. Interior parity, side separation and regional Euler are conclusions of this chain."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Actual cycle orientation fibers and edge restriction also follow from cycle_boundary_walk. This conclusion applies without the signed Euler equation or a connectedness assumption on the ambient rotation. "
                + "It takes an actual Rotation R, a simple closed walk p, a binary face function x, and the equality of its boundary with the edge indicator of p. "
                + "It identifies both shores for every actual dart with p or p.reverse. The following application derives its rotation and face function internally from a permutation; neither is an input assumption.")),
            Paragraph(Text(
                "Fix the original finite labelled vertex type V with at least three vertices and any simple graph F on V. "
                + "Let H(F) consist of the connected simple graphs C on exactly V whose degree is two at every vertex and which contain F. "
                + "Let L(F) contain all actual pairs (E,sigma): E has no edges outside F, chooses exactly one direction of every F edge, and has at most one incoming and one outgoing edge at each vertex; "
                + "sigma is a permutation with IsCycleOn Set.univ, and E(x,y) implies sigma(x)=y. "
                + "This is the entire pair space, including isolated vertices of F; it is not the image of a selected construction. "
                + "A full cycle on at least three vertices has neither fixed points nor two-cycles, by Perm.IsCycleOn.pow_apply_eq. "
                + "Consequently E(x,y) is forced to be F.Adj(x,y) and sigma(x)=y, so the permutation determines the whole pair.")),
            Paragraph(Text(
                "For a raw C in H(F), Mathlib's IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp supplies an actual simple closed walk p. "
                + "Connectedness makes its support all of the original V, and Walk.IsCycle.adj_toSubgraph_iff_of_isCycles makes its edges exactly those of C. "
                + "The permutation of p.support.dropLast, using List.isCycle_formPerm and the actual dart indices, is a full cycle on V and satisfies C.Adj(x,y) if and only if sigma(x)=y or sigma(y)=x. "
                + "Restricting its direction to F constructs an actual E and hence a lift. No orientation, path decomposition, walk, completion or orientation-independence premise is supplied with F or C.")),
            Paragraph(Text(
                "For an arbitrary full-cycle permutation sigma with this same shadow C, the two neighbors at v are sigma(v) and sigma inverse(v), and are distinct. "
                + "Define the rotor to exchange those two outgoing darts at each v. It is an involution, and its orbits are exactly the darts with the same first vertex, so it is an actual Rotation of C. "
                + "Label a dart by one exactly when sigma takes its first vertex to its second vertex, and by zero otherwise. "
                + "The face permutation preserves this label by the two local neighbor cases. Function.Semiconj.iterate_right therefore descends it to the actual face quotient, without a further global propagation argument. "
                + "Opposite darts have opposite labels, so the binary boundary is one on every edge of C. "
                + "Applying cycle_boundary_walk to this derived data and the raw walk p identifies every dart of sigma with p or its reverse. "
                + "Doing this for two arbitrary lifts shows their permutations are equal or inverse; forced orientation then identifies the actual pairs.")),
            Paragraph(Text(
                "The forgetful graph of (E,sigma) has adjacency sigma(x)=y or sigma(y)=x, for all vertex pairs; its diagonal is false. "
                + "It is connected and has degree two, since the full orbit reaches every vertex and its neighbor set is exactly the two distinct neighbors above. "
                + "Reversing E and inverting sigma is an involution with no fixed pair. The preceding raw construction makes the forgetful map onto H(F), and each fiber is exactly a pair and its reversal. "
                + "The generic Setoid.quotientKerEquivOfSurjective identifies the quotient by this actual reversal relation with H(F), sending each class to that same completed graph. "
                + "Thus every revealed adjacency event is preserved, rather than merely a completion count.")),
            Paragraph(Text(
                "For distinct u and v, adding the undirected edge uv gives an equivalence from L(F sup edge(u,v)) to the subtype of L(F) where the same completed graph contains uv. "
                + "The forward map keeps sigma and restricts E to F. Its inverse keeps sigma and takes E(x,y) to be (F sup edge(u,v)).Adj(x,y) and sigma(x)=y. "
                + "Forced orientation proves these maps are inverse and makes the expansion unique. Both maps retain the completed graph and commute with reversal. "
                + "The source graph need not be a forest: the equivalence includes a spanning path with its closing edge added, and F=C. "
                + "In particular all conclusions apply to the original case where F is acyclic with maximum degree at most two; those two restrictions are unnecessary for this correspondence.")),
            Paragraph(Text(
                "The multiplicity of two for a connected simple cycle is classical: Greenhill, Janson, Kim and Wormald, Permutation pseudographs and contiguity, DOI 10.1017/S0963548301005065, page 3, "
                + "gives the permutation multiplicities of two-regular pseudographs. The application here uses ordinary simple cycles with at least three vertices. "
                + "On two vertices inverse permutations coincide, so the distinct-pair conclusion fails. A disconnected union of cycles is not the shadow of a full cycle. "
                + "A permutation taking each vertex to a neighbor can contain two-cycles and need not recover all graph edges; full support in one cycle is essential. "
                + "No small-pseudograph convention, random labels or ports, conditional distribution, adaptive history, alternating count, query complexity or EXIT bound follows from this correspondence.")),
            Paragraph(Text(
                "The two facial subsets are x inverse-image of one and x inverse-image of zero; binary values make them complementary and both are nonempty. "
                + "These results establish face-to-cycle exactness, actual side separation, connected edge-selected regions, both regional Euler identities, directed boundaries, matching restriction and the face-odd nice-cycle orientation. "
                + "Geometric embedding correspondence and arbitrary graph cases, matching-sign transport, compatible Pfaffian expansion, Cayley's identity and nonnegative-weight partition identities including zero cases, rational input and bit complexity, and general bipartite counting complexity remain outside these results. This is an application of mature Kasteleyn theory in the stated finite rotation model; no research originality or full Chapter 30 completion is claimed."))), []));
}
