using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definitions for level sequences and avoidance of the patterns 101 and 102.",
        H("Level Sequence Definitions"),
        Blocks(
            Node("level-sequence-levelsequencedefs-lev", "Level count", "lev",
                "The level of a finite sequence is the number of adjacent equal pairs in the sequence.", DescribeRole.Definition),
            Node("level-sequence-levelsequencedefs-islevel", "Level sequence predicate", "IsLevel",
                "A sequence is a level sequence when its first entry is zero and each later entry is at most one plus the level of its preceding prefix.", DescribeRole.Definition),
            Node("level-sequence-levelsequencedefs-contains101", "Occurrence of 101", "Contains101",
                "A sequence contains 101 when three positions in increasing order carry values with the first and third equal and the middle smaller.", DescribeRole.Definition),
            Node("level-sequence-levelsequencedefs-contains102", "Occurrence of 102", "Contains102",
                "A sequence contains 102 when three positions in increasing order carry values whose first is smaller than the third and whose middle is strictly between them.", DescribeRole.Definition),
            Node("level-sequence-levelsequencedefs-avoiders", "Avoiding level sequences", "avoiders",
                "For a natural number n, the avoiders are the level sequences of length n containing neither 101 nor 102.", DescribeRole.Definition),
            Node("level-sequence-levelsequencedefs-claim", "Catalan counting claim", "claim",
                "For every positive n, the cardinality of the avoiders of length n is the Catalan number at index n.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
