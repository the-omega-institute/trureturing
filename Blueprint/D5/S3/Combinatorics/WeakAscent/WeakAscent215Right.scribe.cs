using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215RightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Right.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive entries and intervening zeros characterize the second Class 215 family.",
        H("The Second Avoidance Class"),
        Blocks(
            Node("weak-ascent-weakascent215right-intrinsic-right-iff", "An intrinsic avoidance criterion", "intrinsic_right_iff",
                "For a word of nonnegative integers whose entry at position zero is zero, using zero also for a missing entry, avoidance of 021, 101, 201 and 210 is equivalent to both of the following conditions. The positive entries in their original order are weakly increasing. Whenever a positive entry precedes a zero and that zero precedes a later entry, the first and last of these three entries are unequal. The empty word is included.", DescribeRole.Theorem),
            Node("weak-ascent-weakascent215right-right-append-iff", "Appending in the second class", "right_append_iff",
                "Let w be a nonempty weak ascent sequence avoiding 021, 101, 201 and 210. A nonnegative letter a can be appended while preserving this class exactly when a is at most one plus the weak ascent count of w and either a is zero, a is greater than the maximum of w, or a equals that maximum and the last entry of w is positive.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
