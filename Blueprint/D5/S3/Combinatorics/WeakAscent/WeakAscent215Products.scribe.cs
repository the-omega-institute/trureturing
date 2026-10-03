using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215ProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Products.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pure-history series records both expenditure and length.",
        H("The Bivariate Pure-History Series"),
        Blocks(
            Node("weak-ascent-weakascent215products-pureseries", "The pure-history series", "pureSeries",
                "The coefficient of z to the power s and x to the power l in P(z,x) is the number of pure histories of expenditure s and length l. Coefficients are nonnegative integers.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
