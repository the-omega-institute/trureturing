using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Embedding finite sets of induced-graph vertices into the original labels preserves cardinalities and averages.",
        H("Transporting residual domination"),
        Blocks(
            Node("residualdomsets", "Full residual domination", "residualDomSets",
                "The dominating sets of the induced residual graph written on the original vertex labels.", DescribeRole.Definition),
            Node("residualdomsets-average", "Preservation of the mean", "residualPartial_average",
                "Embedding the partially dominating residual family preserves its mean size.", DescribeRole.Theorem),
            Node("residualdomsets-subset", "Full domination implies partial domination", "residualDomSets_subset",
                "Internal domination of every residual vertex includes domination of all vertices outside the neighbourhood of the removed stem.", DescribeRole.Theorem),
            Node("residual-equal-of-card-equal", "Equal family sizes", "residual_equal_of_card_equal",
                "A subfamily of equal finite cardinality equals its containing family.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
