using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoTypeIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type I inserts the pivot twice after the upper word and preserves 1322 avoidance.",
        H("Type I Terminal Insertion"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwotypei-typeiword", "Type I word", "typeIWord",
                "The type I word concatenates the upper word, the first cut letters of the lower word, the pivot, the remaining lower letters, and a second pivot.", DescribeRole.Definition),
            Node("nonnesting-nonnestingonethreetwotwotypei-typei-avoids", "Type I preserves 1322 avoidance", "typeI_avoids",
                "Suppose every upper letter exceeds the pivot, every lower letter is smaller than the pivot, each word has exactly two copies of each of its letters, and both words avoid 1322. If every first occurrence in the lower word lies before the cut, the type I word avoids 1322.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
