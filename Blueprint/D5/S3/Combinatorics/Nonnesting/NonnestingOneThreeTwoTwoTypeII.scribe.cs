using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoTypeIIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type II interleaves two copies of a lower order with the upper word and preserves 1322 avoidance.",
        H("Type II Terminal Insertion"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwotypeii-typeiiword", "Type II word", "typeIIWord",
                "The type II word concatenates the first cut letters of the upper word, the lower order, the pivot, the remaining upper letters, the lower order again, and a second pivot.", DescribeRole.Definition),
            Node("nonnesting-nonnestingonethreetwotwotypeii-typeii-avoids", "Type II preserves 1322 avoidance", "typeII_avoids",
                "Suppose every upper letter exceeds the pivot, every letter of the lower order is smaller than the pivot, the upper word has exactly two copies of each of its letters, and the lower order has distinct entries. If the upper word and the concatenation of two copies of the lower order avoid 1322, and every first occurrence in the upper word lies before the cut, the type II word avoids 1322.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
