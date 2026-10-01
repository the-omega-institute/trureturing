using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215RightWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215RightWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The target series counts words in the second Class 215 avoidance family.",
        H("Counting Words in the Second Class"),
        Blocks(
            Node("weak-ascent-weakascent215rightwords-right-word-counts", "Word counts as target coefficients", "right_word_counts",
                "For every nonnegative length n, the number of weak ascent sequences of length n avoiding 021, 101, 201 and 210, viewed as a rational number, is the coefficient of degree n in the target counting series.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
