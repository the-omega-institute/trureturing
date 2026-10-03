using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215LeftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Left.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated values and inversion intervals characterize appending in the first Class 215 family.",
        H("Appending to the First Avoidance Class"),
        Blocks(
            Node("weak-ascent-weakascent215left-repeatedthreshold", "The largest repeated value", "repeatedThreshold",
                "The repeated threshold of a word is its greatest value occurring at least twice, or zero when there is no repeated value.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215left-left-append-iff", "The criterion for appending a letter", "left_append_iff",
                "Let w be a nonempty weak ascent sequence avoiding 100, 101, 110 and 201, and let a be a nonnegative integer. Appending a preserves this avoidance class exactly when a is at least the repeated threshold of w, is at most one plus the weak ascent count of w, and belongs to no closed interval from the lower value to the upper value of an inversion of w.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
