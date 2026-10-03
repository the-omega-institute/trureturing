using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent criteria characterize avoidance of 101 and 102.",
        H("Descent Criteria for Pattern Avoidance"),
        Blocks(
            Node("level-sequence-levelsequencedescent-strong-descent", "Strong descent criterion", "strong_descent",
                "A word avoids 101 and 102 exactly when every descent from an earlier entry to a later smaller entry remains strictly below that earlier entry at all subsequent positions.", DescribeRole.Theorem),
            Node("level-sequence-levelsequencedescent-append-criterion", "Append criterion", "append_criterion",
                "For a nonempty word, appending a letter preserves avoidance of 101 and 102 exactly when the new letter is smaller than every earlier entry that can be the first entry of a forbidden descent pattern.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
