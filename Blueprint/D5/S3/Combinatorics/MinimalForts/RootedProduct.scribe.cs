using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class RootedProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/RootedProduct.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rooted choices on disjoint base graphs.", H("Rooted choices on disjoint base graphs"),
        Blocks(
            Node("rootedchoices-sum-count", "Exact product of the full choice classes", "rootedChoices_sum_count", "For any two finite decidable simple graphs G and H, each without isolated vertices, the full root-containing minimal-fort choice count for their disjoint base sum is the product of the two full rooted choice counts. Closed minimal domination and exclusion of every contained base fort both factor over the components. An injective and exhaustive disjoint-subset map gives the product cardinality.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
