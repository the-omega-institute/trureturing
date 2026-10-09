using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LocalDominatingStemBoundSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LocalDominatingStemBoundSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stem is selected, its leaves are free choices, and the residual set must dominate the vertices not adjacent to the stem.",
        H("The stem-conditioned split"),
        Blocks(
            Node("stem-family-card", "Family size", "stem_family_card",
                "The number of conditioned dominating sets is 2 to the number of leaves times the number of partially dominating residual sets.", DescribeRole.Theorem),
            Node("powerset-card-sum", "Total size of free leaf choices", "powerset_card_sum",
                "Twice the sum of the sizes of all subsets of a finite set is its cardinality times the size of its powerset.", DescribeRole.Theorem),
            Node("avdat-stem-split", "Exact mean split", "avdAt_stem_split",
                "The local mean is one plus half the number of leaf neighbours plus the mean size of the partial residual family.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
