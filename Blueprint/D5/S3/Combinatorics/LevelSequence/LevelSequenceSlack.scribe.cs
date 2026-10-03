using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceSlackDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceSlack.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuations encode the slack above a level sequence prefix.",
        H("Continuation Sets with Slack"),
        Blocks(
            Node("level-sequence-levelsequenceslack-continuations", "Continuation set", "continuations",
                "For slack s and size n, the continuation set consists of words of length n whose entries are bounded by their positions after a prefix of s zero entries and whose patterns avoid 101 and 102.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
