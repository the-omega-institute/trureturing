using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.LevelSequence;

internal sealed class LevelSequenceWordCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/mansour2026wilf");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded avoiding words satisfy a first-letter convolution recurrence.",
        H("Word Counts by Alphabet Size"),
        Blocks(
            Node("level-sequence-levelsequencewordcount-words", "Bounded avoiding words", "words",
                "For alphabet size a and word length n, the word set consists of length-n words with entries below a that avoid 101 and 102.", DescribeRole.Definition),
            Node("level-sequence-levelsequencewordcount-alphabet-recurrence", "Alphabet recurrence", "alphabet_recurrence",
                "The count of bounded avoiding words of length n plus one is the sum over the first letter and the cut position of the product of the two corresponding smaller word counts.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
