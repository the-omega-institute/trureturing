using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentStatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentStates.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum, inversion bottom and weak ascent count control appending a letter.",
        H("States of 210-Avoiding Weak Ascent Sequences"),
        Blocks(
            Node("weak-ascent-weakascentstates-inversionbottom", "The largest inversion bottom", "inversionBottom",
                "The largest inversion bottom of a sequence is the greatest entry that is strictly smaller than an entry at an earlier position, or zero if there is no such entry.", DescribeRole.Definition),
            Node("weak-ascent-weakascentstates-last-extreme", "The last entry is an extreme", "last_extreme",
                "For every nonempty sequence avoiding 210, the largest inversion bottom D is at most both the maximum M and the last entry. The last entry either equals M, or equals D with D strictly less than M.", DescribeRole.Theorem),
            Node("weak-ascent-weakascentstates-append-interval", "The interval of appendable letters", "append_interval",
                "For every nonempty 210-avoiding weak ascent sequence, appending a nonnegative letter x gives another 210-avoiding weak ascent sequence exactly when x is at least the largest inversion bottom and at most one plus the weak ascent count.", DescribeRole.Theorem),
            Node("weak-ascent-weakascentstates-append-state", "State changes under appending", "append_state",
                "For any sequence with maximum M and largest inversion bottom D, appending x changes the maximum to the greater of M and x. The weak ascent count increases by one precisely when the sequence is nonempty and its last entry is at most x. The new largest inversion bottom is the greater of D and x if x is less than M, and is D otherwise; the maximum of the empty sequence is zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
