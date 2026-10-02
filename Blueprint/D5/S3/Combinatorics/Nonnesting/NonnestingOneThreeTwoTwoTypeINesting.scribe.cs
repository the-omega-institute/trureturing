using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoTypeINestingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type I insertion preserves avoidance of both nesting patterns.",
        H("Nonnesting under Type I Insertion"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwotypeinesting-typei-nonnesting", "Type I preserves nonnesting", "typeI_nonnesting",
                "Suppose every upper letter exceeds the pivot, every lower letter is smaller than the pivot, the lower word has exactly two copies of each of its letters, and both words avoid 1221 and 2112. If every first occurrence in the lower word lies before the cut, the type I word also avoids 1221 and 2112.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
