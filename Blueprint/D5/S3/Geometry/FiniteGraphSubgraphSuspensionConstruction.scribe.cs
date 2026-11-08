using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteGraphSubgraphSuspensionConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite star gadget, exact face cover, and coordinate contractions.",
        H("Subgraph suspension construction"),
        Blocks(
            Node("maxindependent", "MaxIndependent", "Maximal independent sets",
                "For a finite simple graph H, MaxIndependent(H) consists of its inclusion-maximal independent finite vertex sets, rather than just the sets of maximum cardinality.", DescribeRole.Definition),
            Node("maximal-extension", "maximal_extension", "Independent extension",
                "Every independent finite vertex set of a finite graph H is contained in a maximal independent set of H.", DescribeRole.Theorem),
            Node("isolated-mem", "isolated_mem", "Isolated vertices are retained",
                "Every isolated H-vertex belongs to every maximal independent set of H. Thus extending H to the ambient vertex set adds no apex adjacency outside its original vertices.", DescribeRole.Theorem),
            Node("suspensiongraph", "suspensionGraph", "The literal star gadget",
                "For finite graphs H and G on V, the gadget has vertices V plus a hub plus one apex for each maximal H-independent set M. On old vertices it retains exactly the G-edges absent from H. The hub is adjacent to every apex and no old vertex. Distinct apices have no edge; the apex of M is adjacent to exactly the old vertices outside M. The homology theorem assumes H is an arbitrary edge subgraph of G and does not require inducedness.", DescribeRole.Definition),
            Node("subgraph-apex-off-vertices", "subgraph_apex_off_vertices", "No outside apex neighbors",
                "For every Mathlib subgraph H of G, every maximal independent set of its spanning graph, and every old vertex outside H.verts, that old vertex has no edge to the corresponding gadget apex.", DescribeRole.Theorem),
            Node("closedstar", "closedStar", "Closed independence stars",
                "For each gadget vertex a, the closed star consists of nonempty independent faces whose vertices are all nonadjacent to a. Adjoining a preserves every such face.", DescribeRole.Definition),
            Node("stara", "starA", "The hub star",
                "A is the closed star of the hub. Its faces contain no apex, and adjoining the hub contracts it.", DescribeRole.Definition),
            Node("starb", "starB", "The independent apex star cluster",
                "B is the union of the closed stars of all the mutually nonadjacent apices. The finite union is defined by the actual faces of those stars.", DescribeRole.Definition),
            Node("cover-faces", "cover_faces", "The literal face cover",
                "For every pair of finite graphs G,H on V, the actual gadget independence complex equals A union B. A face containing an apex belongs to that apex star, and a face containing none belongs to the hub star.", DescribeRole.Theorem),
            Node("intersection-faces", "intersection_faces", "Exact old intersection",
                "For every H less than or equal to G, A intersect B equals the old-vertex embedding of the actual independence complex of G. Both retained edges in G minus H and H-edges remain constraints in this intersection. Arbitrary noninduced H is included.", DescribeRole.Theorem),
            Node("coordinates-mass", "mass", "Total apex mass",
                "For every real gadget coordinate vector x, mass(x) is the finite sum of the coordinates at all apices.", DescribeRole.Definition),
            Node("coordinates-bad", "bad", "Mass outside one apex star",
                "For each maximal H-independent set M, b_M(x) is the hub coordinate plus the sum of all old coordinates outside M.", DescribeRole.Definition),
            Node("coordinates-delta", "delta", "A continuous finite minimum",
                "Delta(x) is the minimum of b_M(x) over the nonempty finite family of maximal H-independent sets. Continuity follows from finite minima; the maps never select an argmin. For nonnegative vectors delta vanishes exactly when the hub and every old coordinate outside some M vanish.", DescribeRole.Definition),
            Node("coordinates-starb-realization-iff", "starB_realization_iff", "The cluster zero set",
                "For every real gadget coordinate vector x, membership in the realized apex star cluster is equivalent to membership in the actual gadget independence realization together with delta(x)=0.", DescribeRole.Theorem),
            Node("coordinates-epsilon", "epsilon", "The fixed threshold",
                "Write N for the total number of gadget vertices. The fixed threshold is epsilon=1/(4(N+1)); it is strictly positive and N epsilon is strictly less than one quarter.", DescribeRole.Definition),
            Node("coordinates-u", "U", "The first actual open set",
                "Inside the actual gadget independence realization X, U is the set of points with total apex mass strictly less than one half.", DescribeRole.Definition),
            Node("coordinates-o", "O", "The second actual open set",
                "Inside X, O is the set where delta is strictly less than epsilon. These sets are open in the actual subspace topology.", DescribeRole.Definition),
            Node("coordinates-open-cover", "open_cover", "An actual open cover",
                "For every pair of finite graphs G,H, U union O is all of X. Positive apex mass forces b_M=0 at an occupied apex, and hence delta=0.", DescribeRole.Theorem),
            Node("coordinates-contractible-u", "contractible_U", "Contraction of the first open set",
                "Erase all apex coordinates and normalize, then interpolate to the hub. Both stages remain in U and in the actual independence realization. This constructs contractibility of U for all finite G,H.", DescribeRole.Theorem),
            Node("coordinates-contractible-starb", "contractible_starB", "Contraction of the closed star cluster",
                "Apply the fixed epsilon cutoff and normalize. Then interpolate to the compatible apex probability vector with unnormalized weights max(epsilon-b_M,0), and finally to a fixed apex. The fixed cutoff denominator exceeds three quarters. At least one apex weight is at least epsilon-delta, hence strictly positive in O. The support tests preserve actual independence and delta=0 throughout the contraction on B. This constructs contractibility of the actual finite apex star cluster.", DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
