using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class CambieQ19GraphDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Graph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The graph has a 5,000-cycle, two 500-vertex paths attached at cycle vertices 0 and 1,000, and a triangle attached at vertex 500. Each attachment is a single bridge to vertex 0 in its block.",
        H("The cycle, paths and triangle of the counterexample"),
        Blocks(
            Node("join-at", "joinAt", "Joining two graphs at designated vertices",
                "The disjoint sum gains the edge from the designated left vertex to the designated right vertex.", DescribeRole.Definition),
            Node("join-at-inl", "joinAt_inl", "Left adjacency",
                "Two left vertices are adjacent exactly when they are adjacent in the left graph.", DescribeRole.Theorem),
            Node("join-at-inr", "joinAt_inr", "Right adjacency",
                "Two right vertices are adjacent exactly when they are adjacent in the right graph.", DescribeRole.Theorem),
            Node("join-at-cross", "joinAt_cross", "Cross adjacency",
                "A left vertex and a right vertex are adjacent exactly when both are the designated endpoints.", DescribeRole.Theorem),
            Node("vertex", "Vertex", "The 6,003 labeled vertices",
                "The vertex set is the disjoint sum of the 5,000 core positions, two sets of 500 path positions and three triangle positions.", DescribeRole.Definition),
            Node("core", "core", "Core positions",
                "The inclusion sends each of the 5,000 core positions to its vertex in the disjoint sum.", DescribeRole.Definition),
            Node("first-path", "firstPath", "First path positions",
                "The inclusion sends each of the 500 first-path positions to its vertex in the disjoint sum.", DescribeRole.Definition),
            Node("second-path", "secondPath", "Second path positions",
                "The inclusion sends each of the 500 second-path positions to its vertex in the disjoint sum.", DescribeRole.Definition),
            Node("triangle", "triangle", "Triangle positions",
                "The inclusion sends each of the three triangle positions to its vertex in the disjoint sum.", DescribeRole.Definition),
            Node("g500", "G500", "The witness graph",
                "Join the 5,000-cycle first to the path at 0, then to the path at 1,000, and then to the triangle at 500, in each case using position 0 in the attached block.", DescribeRole.Definition),
            Node("g500-connected", "G500_connected", "Connectedness of the witness",
                "Paths inside the four blocks and the three joining edges connect all vertices of the witness graph.", DescribeRole.Theorem),
            Node("left-set", "leftSet", "Restriction to the left vertices",
                "Take the preimage of the support under the left inclusion.", DescribeRole.Definition),
            Node("right-set", "rightSet", "Restriction to the right vertices",
                "Take the preimage of the support under the right inclusion.", DescribeRole.Definition),
            Node("split-iso", "splitIso", "Splitting an induced vertex type",
                "The disjoint sum of the two support restrictions is isomorphic to the induced graph via the canonical sum equivalence and pullback of adjacency.", DescribeRole.Definition),
            Node("split-graph-inl", "splitGraph_inl", "Left induced graph",
                "Pulling back the induced join to the left restriction gives the corresponding induced left graph.", DescribeRole.Theorem),
            Node("split-graph-inr", "splitGraph_inr", "Right induced graph",
                "Pulling back the induced join to the right restriction gives the corresponding induced right graph.", DescribeRole.Theorem),
            Node("split-graph-cross", "splitGraph_cross", "Cross adjacency in the induced graph",
                "The cross edge is present between two selected endpoints exactly when they are the designated joining vertices.", DescribeRole.Theorem),
            Node("join-at-induce-connected", "joinAt_induce_connected", "Induced connectivity across one bridge",
                "An induced support is connected exactly when it is nonempty, its two side restrictions are preconnected, and the designated endpoints are both selected whenever both sides are nonempty.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
