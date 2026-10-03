using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackContinuation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a word p, W(p) prepends one more than its second entry and increases by one each original entry larger than that second entry. Positions are numbered from zero, and an absent entry is read as zero.",
        H("Ordinary continuation"),
        Blocks(
            Node("pop-stack-popstackcontinuation-w", "Ordinary continuation", "W",
                "For a word p, W(p) prepends one more than its second entry and increases by one each original entry larger than that second entry. Positions are numbered from zero, and an absent entry is read as zero.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
