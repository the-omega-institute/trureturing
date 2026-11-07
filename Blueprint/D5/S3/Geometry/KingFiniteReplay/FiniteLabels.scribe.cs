using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KingFiniteReplayFiniteLabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KingFiniteReplay/FiniteLabels.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite labels and exact adjacency rows", H("Finite labels and exact adjacency rows"), Blocks(
            Node("n0", "listGraph", "An edge-list graph",
                "The finite graph on a specified finite set of natural labels has exactly the unordered pairs listed as edges, with loops excluded."),
            Node("n1", "rowBits_spec", "Exact bit-row meaning",
                "Bit y in row x is set precisely when an orientation of the pair x,y occurs in the original edge list."),
            Node("n2", "cachedAdjDecidable", "Verified row evaluation",
                "An equality proof between cached rows and the original row function yields a decision procedure for the original graph adjacency; the graph definition is unchanged."),
            Node("n3", "sumLabels", "Old and fresh labels",
                "Injective old and fresh label functions with disjoint images, all landing in the target finite set and jointly covering it, give an equivalence from their sum carrier to the target labels."),
            Node("n4", "map_eq_of_forward", "Graph equality after relabeling",
                "An adjacency equivalence checked in the forward direction identifies the relabeled graph with the given target graph."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
