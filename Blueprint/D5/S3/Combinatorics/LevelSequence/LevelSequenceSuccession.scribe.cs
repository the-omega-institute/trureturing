using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceSuccessionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceSuccession.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The succession relation for slack continuations gives the Catalan generating series.",
        H("Slack Succession"),
        Blocks(
            Node("level-sequence-levelsequencesuccession-slack-succession", "Slack succession", "slack_succession",
                "For a nonempty avoiding tail, the slack values of all admissible successors are obtained by the successive cuts determined by the tail and its initial spine.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
