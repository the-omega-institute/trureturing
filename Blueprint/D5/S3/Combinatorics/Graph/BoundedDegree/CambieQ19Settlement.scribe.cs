using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class CambieQ19SettlementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/cambiejookenwagner2026meansubtrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected vertex support is an interval with permitted attachments or is confined to one attached block.",
        H("Connected induced supports and the two means"),
        Blocks(
            Node("subtrees-of-order", "SubtreesOfOrder", "Actual tree subgraphs of a given order",
                "Choose a subgraph whose graph on its own vertices is a tree and whose vertex count is the specified order. The vertices and edges are both part of the subgraph.", DescribeRole.Definition),
            Node("subtree-count", "subtreeCount", "Subtree counts by order",
                "The count at order k is the cardinality of the type of actual tree subgraphs with k vertices.", DescribeRole.Definition),
            Node("total-subtree-count", "totalSubtreeCount", "Total subtree count",
                "Sum the counts at all natural orders from one through the host cardinality.", DescribeRole.Definition),
            Node("total-subtree-order", "totalSubtreeOrder", "Total subtree order",
                "Sum the product of the order and its subtree count from order one through the host cardinality.", DescribeRole.Definition),
            Node("mean-subtree-order", "meanSubtreeOrder", "Mean order of tree subgraphs",
                "Divide total subtree order by the total subtree count in the rationals.", DescribeRole.Definition),
            Node("connected-sets", "ConnectedSets", "Connected vertex sets",
                "A vertex set is counted once when its induced graph is connected.", DescribeRole.Definition),
            Node("mean-connected-order", "meanConnectedOrder", "Mean order of connected vertex sets",
                "For a finite vertex type, divide the sum of the connected-set cardinalities by their count in the rationals.", DescribeRole.Definition),
            Node("claim", "claim", "Question 1.9",
                "Cambie, Jooken and Wagner ask whether the subtree mean is at least the connected-set mean for every connected graph. The quantification is over finite simple graphs. Singletons contribute to both means.", DescribeRole.Definition),
            Node("cycle-interval", "CycleInterval", "Cyclic intervals",
                "The code is either the full cycle or a starting vertex and a positive length strictly smaller than the cycle size.", DescribeRole.Definition),
            Node("cycle-vertices", "cycleVertices", "Vertices of a cyclic interval",
                "The full cycle uses every core vertex. A proper cyclic interval uses successive vertices from its start.", DescribeRole.Definition),
            Node("cycle-order", "cycleOrder", "Order of a cyclic interval",
                "The order is the cycle size or the encoded positive length.", DescribeRole.Definition),
            Node("path-order", "order", "Order of a path interval",
                "The order is the difference of the endpoints plus one.", DescribeRole.Definition),
            Node("path-interval", "PathInterval", "Intervals in a path",
                "An interval is given by its two path positions in weakly increasing order, both included.", DescribeRole.Definition),
            Node("induced-connected-of-preconnected", "induced_connected_of_preconnected", "Preconnected nonempty supports",
                "An induced subgraph on a nonempty vertex subset is connected whenever it is preconnected.", DescribeRole.Theorem),
            Node("path-prefix", "PathPrefix", "Permitted path prefixes",
                "The prefix length is between zero and 500. A positive length requires selection of the path mark in the core.", DescribeRole.Definition),
            Node("triangle-extension", "TriangleExtension", "Permitted triangle subsets",
                "A nonempty triangle subset requires selection of core vertex 500 and triangle vertex 0.", DescribeRole.Definition),
            Node("configuration", "Configuration", "The four support configurations",
                "Choose a core interval with its permitted attachments, an interval of the first path alone, an interval of the second path alone, or a nonempty subset of the triangle alone.", DescribeRole.Definition),
            Node("core-set", "coreSet", "Projection to core vertices",
                "Take the preimage of a support under the core inclusion.", DescribeRole.Definition),
            Node("triangle-set", "triangleSet", "Projection to triangle vertices",
                "Take the preimage of a support under the triangle inclusion.", DescribeRole.Definition),
            Node("vertices", "vertices", "Vertices of a decoded configuration",
                "Take the core interval together with its selected attachments, or the indicated support in a single attached block.", DescribeRole.Definition),
            Node("vertex-order", "vertexOrder", "Order of the decoded configuration",
                "For a support meeting the core, add the core interval length, the two prefix lengths and the triangle cardinality. Otherwise use the order of the selected interval or triangle subset.", DescribeRole.Definition),
            Node("support-connected", "supportConnected", "Connectedness of the decoded support",
                "Each of the four configurations induces a connected subgraph of the witness.", DescribeRole.Theorem),
            Node("support-equiv", "supportEquiv", "The connected-support equivalence",
                "Decoding gives a bijection from the four interval-and-attachment cases to all actual connected induced supports of the witness.", DescribeRole.Definition),
            Node("support-equiv-symm-verts", "supportEquiv_symm_verts", "Vertex set of the inverse image",
                "The inverse equivalence sends a configuration to the connected induced support whose vertex set is its decoded set.", DescribeRole.Theorem),
            Node("support-equiv-order", "supportEquiv_order", "Pointwise preservation of support order",
                "The cardinality of the connected support recovered from each configuration equals its decoded order.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(),
            declaration is "SubtreesOfOrder" or "subtreeCount" or "totalSubtreeCount" or "totalSubtreeOrder"
                or "meanSubtreeOrder" or "ConnectedSets" or "meanConnectedOrder" or "claim"
                ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
