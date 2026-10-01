using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215SitesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Sites.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appendable letters in the first class separate into new records, the current maximum and lower sites.",
        H("Active Letters in the First Class"),
        Blocks(
            Node("weak-ascent-weakascent215sites-left-active-structure", "Structure of appendable letters", "left_active_structure",
                "Let w be a nonempty weak ascent sequence avoiding 100, 101, 110 and 201, with maximum M and last entry L. The bound one plus the weak ascent count is strictly greater than M. Every integer strictly above M and at most that bound is appendable and does not occur in w. The letter M is appendable exactly when L = M. Every appendable letter at most M other than M is strictly less than L.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
