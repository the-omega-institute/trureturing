using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The residual graph has no isolated vertices when the original graph has none.",
        H("Deleting a stem and its leaves"),
        Blocks(
            Node("remaining", "Residual vertices", "remaining",
                "Remove the specified vertex and all its leaf neighbours.", DescribeRole.Definition),
            Node("remaining-neighbor", "A retained neighbour", "remaining_neighbor",
                "A residual vertex has a neighbour other than the removed stem; that neighbour cannot be one of the removed leaves.", DescribeRole.Theorem),
            Node("residualgraph-no-isolates", "Residual absence of isolates", "residualGraph_no_isolates",
                "Each vertex of the induced residual graph has an adjacent residual vertex.", DescribeRole.Theorem),
            Node("remaining-card", "Order decomposition", "remaining_card",
                "The graph order is the residual order plus the number of removed leaves plus one.", DescribeRole.Theorem),
            Node("partialdomsets", "Partial residual domination", "partialDomSets",
                "Require internal domination only for residual vertices not adjacent to the removed stem.", DescribeRole.Definition)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
