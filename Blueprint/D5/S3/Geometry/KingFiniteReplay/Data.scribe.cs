using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KingFiniteReplayDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KingFiniteReplay/Data.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal forty-one finite graph states", H("The literal forty-one finite graph states"), Blocks(
            Node("n1", "graph40", "The final finite graph",
                "The forty moves consist of ten triple subdivisions, five matching suspensions and twenty-five Lozin replacements. The final literal natural-labeled graph has 141 vertices and 178 edges. Every state is specified by its original edge list and an exactly equal adjacency-row function."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
