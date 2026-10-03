using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215WordHistoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing active values and their occurrence marks associate a Boolean stack with a word.",
        H("Active Values and Occurrence Marks"),
        Blocks(
            Node("weak-ascent-weakascent215wordhistory-activevalues", "The increasing active-value list", "activeValues",
                "For a word w, the active-value list consists, in increasing order, of the nonnegative values at most its maximum that can be appended to give a weak ascent sequence of length one more avoiding 100, 101, 110 and 201. The maximum of the empty word is taken to be zero.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215wordhistory-activemarks", "Occurrence marks of active values", "activeMarks",
                "The active-mark list replaces each entry of the increasing active-value list by true when that value occurs in the original word and by false otherwise.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
